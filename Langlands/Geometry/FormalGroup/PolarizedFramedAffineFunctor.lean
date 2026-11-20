import Langlands.Geometry.FormalGroup.PolarizedFramedAffineBaseChange
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyCoefficientCoherence
import Langlands.Geometry.FormalGroup.DrinfeldFramedResidueCoherence

/-! # The affine polarized framed class functor on Nilp -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R S B : Type v} [CommRing R] [CommRing S] [CommRing B]
variable [Algebra O R] [Algebra O S] [Algebra O B]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' σ'' τ'' : Type}
variable [Finite σ] [Finite τ] [Finite σ'] [Finite τ'] [Finite σ''] [Finite τ'']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}
variable {M'' : ModuleLaw O R σ''} {N'' : ModuleLaw O R τ''}

private abbrev Iso.HasIdentityCoordinates {L L' : ModuleLaw O R σ} (e : Iso L L') : Prop :=
  e.hom.toHom.toCoordinateMap = CoordinateMap.id

private theorem Iso.HasIdentityCoordinates.trans {L L' L'' : ModuleLaw O R σ}
    {e : Iso L L'} {f : Iso L' L''} (he : e.HasIdentityCoordinates)
    (hf : f.HasIdentityCoordinates) : (e.trans f).HasIdentityCoordinates := by
  change f.hom.toHom.toCoordinateMap.comp e.hom.toHom.toCoordinateMap = CoordinateMap.id
  rw [he, hf, CoordinateMap.id_comp]

private theorem Iso.HasIdentityCoordinates.map {L L' : ModuleLaw O R σ}
    {e : Iso L L'} (he : e.HasIdentityCoordinates) (φ : R →ₐ[O] S) :
    (e.map φ).HasIdentityCoordinates := by
  change e.hom.toHom.toCoordinateMap.map φ.toRingHom = CoordinateMap.id
  rw [he, CoordinateMap.map_id]

private theorem Iso.eq_of_identityCoordinates {L L' : ModuleLaw O R σ} {e f : Iso L L'}
    (he : e.HasIdentityCoordinates) (hf : f.HasIdentityCoordinates) : e = f :=
  Iso.ext_hom (Hom.ext (CommLaw.Hom.ext (Eq.trans he hf.symm)))

private def mapCompAlongIso (L : ModuleLaw O R σ) (φ : R →ₐ[O] S) (ψ : S →ₐ[O] B)
    {χ : R →ₐ[O] B} (h : χ = ψ.comp φ) : Iso ((L.map φ).map ψ) (L.map χ) := by
  subst χ
  exact mapCompIso L φ ψ

private theorem mapCompAlongIso_coordinates (L : ModuleLaw O R σ)
    (φ : R →ₐ[O] S) (ψ : S →ₐ[O] B) {χ : R →ₐ[O] B} (h : χ = ψ.comp φ) :
    (mapCompAlongIso L φ ψ h).HasIdentityCoordinates := by
  subst χ
  rfl

namespace RationalSection

/-- Successive transport is transport by the composites of the integral comparisons. -/
theorem transportIso_trans (a : Iso M M') (b : Iso N N') (a' : Iso M' M'')
    (b' : Iso N' N'') {U : Opens (PrimeSpectrum R)} (z : RationalSection F M N U) :
    transportIso a' b' U (transportIso a b U z) =
      transportIso (a.trans a') (b.trans b') U z := by
  change comp (ofHom b'.hom U)
      (comp (comp (ofHom b.hom U) (comp z (ofHom a.inv U))) (ofHom a'.inv U)) =
    comp (ofHom (b'.hom.comp b.hom) U) (comp z (ofHom (a.inv.comp a'.inv) U))
  simp only [← comp_ofHom, comp_assoc]

/-- Postcomposing by an integral isomorphism composes the target comparison. -/
theorem comp_transportIso (a : Iso M M') (b : Iso N N') (e : Iso N' N'')
    {U : Opens (PrimeSpectrum R)} (z : RationalSection F M N U) :
    comp (ofHom e.hom U) (transportIso a b U z) = transportIso a (b.trans e) U z := by
  change comp (ofHom e.hom U) (comp (ofHom b.hom U) (comp z (ofHom a.inv U))) =
    comp (ofHom (e.hom.comp b.hom) U) (comp z (ofHom a.inv U))
  rw [← comp_assoc, comp_ofHom]

private theorem baseChange_top_identity_transport (φ : R →ₐ[O] R) (h : φ = AlgHom.id O R)
    (a : Iso (M.map φ) M) (b : Iso (N.map φ) N)
    (ha : a.HasIdentityCoordinates) (hb : b.HasIdentityCoordinates)
    (z : RationalSection F M N ⊤) :
    transportIso a b ⊤ (baseChange φ ⊤ z) = z := by
  subst φ
  rw [a.eq_of_identityCoordinates ha (f := mapIdIso M) rfl,
    b.eq_of_identityCoordinates hb (f := mapIdIso N) rfl]
  exact baseChange_identity_transport ⊤ z

private theorem baseChange_top_composite_transport (φ : R →ₐ[O] S) (ψ : S →ₐ[O] B)
    {χ : R →ₐ[O] B} (h : χ = ψ.comp φ) (z : RationalSection F M N ⊤) :
    transportIso (mapCompAlongIso M φ ψ h) (mapCompAlongIso N φ ψ h) ⊤
      (baseChange ψ ⊤ (baseChange φ ⊤ z)) = baseChange χ ⊤ z := by
  subst χ
  have hz := baseChange_composite_transport φ ψ ⊤ z
  have he : eqToHom (coefficientOpenMap_comp_obj φ ψ ⊤) = 𝟙 (⊤ : Opens (PrimeSpectrum B)) :=
    Subsingleton.elim _ _
  rw [he] at hz
  exact hz.trans (restrict_id ⊤ _)

end RationalSection

end Langlands.FormalGroup.ModuleLaw

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open CategoryTheory ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T U V : Nilp.{0, 0} W π}
variable (X : PolarizedFramedAffinePoint prime π frame T)

private theorem sourceComparison_coordinates (j : T ⟶ U) :
    (sourceComparison (frame := frame) j).orderIso.toModuleIso.HasIdentityCoordinates := by
  apply Iso.HasIdentityCoordinates.trans
  · rfl
  · rfl

private theorem targetComparison_coordinates (j : T ⟶ U) :
    (X.targetComparison j).orderIso.toModuleIso.HasIdentityCoordinates := rfl

/-- Identity base extension is isomorphic to the original framed triple. -/
def baseChangeIdIso : Iso (X.baseChange (𝟙 T)) X where
  targetIso := X.target.mapIdIso
  square := by
    let j := 𝟙 T
    let ψ := Nilp.reducedScalarMap ℤ_[prime] j
    let a := (sourceComparison (frame := frame) j).orderIso.toModuleIso
    let b := (X.targetComparison j).orderIso.toModuleIso
    let e := (X.target.mapIdIso.orderIso.toModuleIso).map (Nilp.quotientO ℤ_[prime] T)
    have h := RationalSection.baseChange_top_identity_transport ψ (Nilp.reducedScalarMap_id _ T)
      a (b.trans e) (sourceComparison_coordinates j)
      ((X.targetComparison_coordinates j).trans (Iso.HasIdentityCoordinates.map (e :=
        X.target.mapIdIso.orderIso.toModuleIso) rfl _)) X.rho
    exact (RationalSection.comp_transportIso a b e (RationalSection.baseChange ψ ⊤ X.rho)).trans h

/-- Successive base extensions are isomorphic to extension along the composite. -/
def baseChangeCompIso (j : T ⟶ U) (k : U ⟶ V) :
    Iso ((X.baseChange j).baseChange k) (X.baseChange (j ≫ k)) where
  targetIso := X.target.mapCompIso (Nilp.scalarMap ℤ_[prime] j) (Nilp.scalarMap ℤ_[prime] k)
  square := by
    let φ := Nilp.reducedScalarMap ℤ_[prime] j
    let ψ := Nilp.reducedScalarMap ℤ_[prime] k
    let hm := Nilp.reducedScalarMap_comp ℤ_[prime] j k
    let a₁ := (sourceComparison (frame := frame) j).orderIso.toModuleIso
    let a₂ := (sourceComparison (frame := frame) k).orderIso.toModuleIso
    let a₃ := (sourceComparison (frame := frame) (j ≫ k)).orderIso.toModuleIso
    let b₁ := (X.targetComparison j).orderIso.toModuleIso
    let b₂ := ((X.baseChange j).targetComparison k).orderIso.toModuleIso
    let b₃ := (X.targetComparison (j ≫ k)).orderIso.toModuleIso
    let e := (X.target.mapCompIso (Nilp.scalarMap ℤ_[prime] j)
      (Nilp.scalarMap ℤ_[prime] k)).orderIso.toModuleIso.map (Nilp.quotientO ℤ_[prime] V)
    let a₀ := mapCompAlongIso (source (frame := frame) (T := T)).law φ ψ hm
    let b₀ := mapCompAlongIso X.reducedTarget.law φ ψ hm
    let z := RationalSection.baseChange φ ⊤ X.rho
    have hz := RationalSection.baseChange_transportIso ψ a₁ b₁ z
    change RationalSection.baseChange ψ ⊤ (RationalSection.transportIso a₁ b₁ ⊤ z) =
      RationalSection.transportIso (a₁.map ψ) (b₁.map ψ) ⊤ (RationalSection.baseChange ψ ⊤ z) at hz
    have ha : (a₁.map ψ).trans a₂ = a₀.trans a₃ :=
      Iso.eq_of_identityCoordinates
        (((sourceComparison_coordinates j).map ψ).trans (sourceComparison_coordinates k))
        ((mapCompAlongIso_coordinates _ φ ψ hm).trans (sourceComparison_coordinates (j ≫ k)))
    have hb : (b₁.map ψ).trans (b₂.trans e) = b₀.trans b₃ :=
      Iso.eq_of_identityCoordinates
        (((X.targetComparison_coordinates j).map ψ).trans
          (((X.baseChange j).targetComparison_coordinates k).trans
            (Iso.HasIdentityCoordinates.map (e := (X.target.mapCompIso (Nilp.scalarMap ℤ_[prime] j)
              (Nilp.scalarMap ℤ_[prime] k)).orderIso.toModuleIso) rfl _)))
        ((mapCompAlongIso_coordinates _ φ ψ hm).trans (X.targetComparison_coordinates (j ≫ k)))
    let q := RationalSection.baseChange ψ ⊤ z
    let q' := RationalSection.transportIso (a₁.map ψ) (b₁.map ψ) ⊤ q
    have pullback := congrArg (fun f => RationalSection.comp (RationalSection.ofHom e.hom ⊤)
      (RationalSection.transportIso a₂ b₂ ⊤ f)) hz
    have postcompose := RationalSection.comp_transportIso a₂ b₂ e q'
    have combine := RationalSection.transportIso_trans (a₁.map ψ) (b₁.map ψ) a₂ (b₂.trans e) q
    have compare := congrArg₂ (fun a b => RationalSection.transportIso a b ⊤ q) ha hb
    have separate := (RationalSection.transportIso_trans a₀ b₀ a₃ b₃ q).symm
    have composite := congrArg (RationalSection.transportIso a₃ b₃ ⊤)
      (RationalSection.baseChange_top_composite_transport φ ψ hm X.rho)
    exact pullback.trans (postcompose.trans (combine.trans (compare.trans (separate.trans composite))))

/-- Pullback descends to classes of actual polarized framed isomorphisms. -/
def IsomorphismClass.baseChange (q : IsomorphismClass (frame := frame) (T := T)) (j : T ⟶ U) :
    IsomorphismClass (frame := frame) (T := U) := by
  refine Quotient.map (fun X : PolarizedFramedAffinePoint prime π frame T => X.baseChange j) ?_ q
  intro X Y h
  change Nonempty (Iso X Y) at h
  exact h.map (fun e => e.baseChange j)

@[simp]
theorem IsomorphismClass.baseChange_id (q : IsomorphismClass (frame := frame) (T := T)) :
    q.baseChange (𝟙 T) = q := by
  induction q using Quotient.inductionOn with
  | h X => exact Quotient.sound ⟨X.baseChangeIdIso⟩

theorem IsomorphismClass.baseChange_comp (q : IsomorphismClass (frame := frame) (T := T))
    (j : T ⟶ U) (k : U ⟶ V) : (q.baseChange j).baseChange k = q.baseChange (j ≫ k) := by
  induction q using Quotient.inductionOn with
  | h X => exact Quotient.sound ⟨X.baseChangeCompIso j k⟩

/-- The covariant functor of affine polarized framed isomorphism classes on Nilp algebras. -/
def classFunctor
    (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])) :
    Nilp.{0, 0} W π ⥤ Type (max 1 w) where
  obj T := IsomorphismClass (frame := frame) (T := T)
  map j := ↾(fun q => q.baseChange j)
  map_id _ := by
    ext q
    exact q.baseChange_id
  map_comp j k := by
    ext q
    exact (q.baseChange_comp j k).symm

/-- On a representative the functor is the actual coefficient extension. -/
@[simp]
theorem classFunctor_map_mk (j : T ⟶ U) :
    (classFunctor frame).map j (Quotient.mk _ X) = Quotient.mk _ (X.baseChange j) := rfl

end Langlands.FormalGroup.PolarizedFramedAffinePoint
