import Langlands.Geometry.FormalGroup.PolarizedFramedAffineFunctor

/-! # Coefficient squares for polarized affine framed classes -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.Iso

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {ι : Type} [Finite ι]
variable {M N P : ModuleLaw O R ι}

private abbrev IdentityCoordinates (a : Iso M N) : Prop :=
  a.hom.toHom.toCoordinateMap = CoordinateMap.id

private theorem IdentityCoordinates.trans {a : Iso M N} {b : Iso N P}
    (ha : a.IdentityCoordinates) (hb : b.IdentityCoordinates) :
    (a.trans b).IdentityCoordinates := by
  change b.hom.toHom.toCoordinateMap.comp a.hom.toHom.toCoordinateMap = CoordinateMap.id
  rw [ha, hb, CoordinateMap.id_comp]

private theorem IdentityCoordinates.map {a : Iso M N} (ha : a.IdentityCoordinates)
    (φ : R →ₐ[O] S) : (a.map φ).IdentityCoordinates := by
  change a.hom.toHom.toCoordinateMap.map φ.toRingHom = CoordinateMap.id
  rw [ha, CoordinateMap.map_id]

private theorem eq_of_identity {a b : Iso M N} (ha : a.IdentityCoordinates)
    (hb : b.IdentityCoordinates) : a = b :=
  Iso.ext_hom (Hom.ext (CommLaw.Hom.ext (Eq.trans ha (Eq.symm hb))))

end Langlands.FormalGroup.ModuleLaw.Iso

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open CategoryTheory ModuleLaw Langlands.Shimura TopologicalSpace _root_.AlgebraicGeometry

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {frame frame' frame'' : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T U V : Nilp.{0, 0} W π}

/-- A square of coefficient maps over the fixed ℤₚ scalars with a specified polarized
isometry from the extended framing source to the new framing source. -/
structure CoefficientChange
    (frame frame' : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime]))
    (T U : Nilp.{0, 0} W π) where
  scalar : T.obj →ₐ[ℤ_[prime]] U.obj
  reduced : ((Nilp.reductionFunctor W π).obj T).obj →ₐ[ℤ_[prime]]
    ((Nilp.reductionFunctor W π).obj U).obj
  quotientSquare : reduced.comp (Nilp.quotientO ℤ_[prime] T) =
    (Nilp.quotientO ℤ_[prime] U).comp scalar
  sourceIso : PolarizedOrderModule.Iso ((source (frame := frame) (T := T)).map reduced)
    (source (frame := frame') (T := U))

namespace CoefficientChange

/-- An ordinary Nilp morphism gives its scalar and quotient square. -/
def ofHom (frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime]))
    (j : T ⟶ U) : CoefficientChange frame frame T U where
  scalar := Nilp.scalarMap ℤ_[prime] j
  reduced := Nilp.reducedScalarMap ℤ_[prime] j
  quotientSquare := (Nilp.quotientO_natural _ j).symm
  sourceIso := sourceComparison (frame := frame) j

/-- The square gives the comparison between the two reduced polarized targets. -/
def targetIso (c : CoefficientChange frame frame' T U)
    (X : PolarizedFramedAffinePoint prime π frame T) :
    PolarizedOrderModule.Iso (X.reducedTarget.map c.reduced)
      ((X.target.map c.scalar).map (Nilp.quotientO ℤ_[prime] U)) :=
  X.target.mapSquareIso (Nilp.quotientO ℤ_[prime] T) c.reduced c.scalar
    (Nilp.quotientO ℤ_[prime] U) c.quotientSquare

/-- Compose coefficient squares and their integral framing comparisons. -/
def comp (c : CoefficientChange frame frame' T U) (d : CoefficientChange frame' frame'' U V) :
    CoefficientChange frame frame'' T V where
  scalar := d.scalar.comp c.scalar
  reduced := d.reduced.comp c.reduced
  quotientSquare := by
    rw [AlgHom.comp_assoc, c.quotientSquare, ← AlgHom.comp_assoc, d.quotientSquare, AlgHom.comp_assoc]
  sourceIso := ((source (frame := frame) (T := T)).mapCompIso c.reduced d.reduced).symm.trans
    ((c.sourceIso.map d.reduced).trans d.sourceIso)

/-- Two squares agree if their coefficient maps and framing comparison coordinates agree. -/
theorem eq_of_maps {c d : CoefficientChange frame frame' T U}
    (hs : c.scalar = d.scalar) (hr : c.reduced = d.reduced)
    (hc : c.sourceIso.orderIso.hom.val.toHom.toCoordinateMap =
      d.sourceIso.orderIso.hom.val.toHom.toCoordinateMap) : c = d := by
  cases c with
  | mk cs cr cq ci =>
    cases d with
    | mk ds dr dq di =>
      change cs = ds at hs
      change cr = dr at hr
      subst ds
      subst dr
      have hi : ci.orderIso = di.orderIso :=
        OrderAction.Iso.ext_hom (Subtype.ext (Hom.ext (CommLaw.Hom.ext hc)))
      cases ci with
      | mk co hp =>
        cases di with
        | mk do' hq =>
          change co = do' at hi
          subst do'
          rfl

end CoefficientChange

variable (X : PolarizedFramedAffinePoint prime π frame T)

/-- Extend the polarized target and its actual framing along a coefficient square. -/
def mapCoefficients (c : CoefficientChange frame frame' T U) :
    PolarizedFramedAffinePoint prime π frame' U where
  target := X.target.map c.scalar
  rho := RationalSection.transportIso c.sourceIso.orderIso.toModuleIso
    (c.targetIso X).orderIso.toModuleIso ⊤ (RationalSection.baseChange c.reduced ⊤ X.rho)
  commutes a := by
    let e := c.sourceIso.orderIso
    let f := (c.targetIso X).orderIso
    have h := congrArg (RationalSection.baseChange c.reduced ⊤) (X.commutes a)
    simp only [RationalSection.baseChange_comp, RationalSection.baseChange_ofHom] at h
    change RationalSection.comp (RationalSection.baseChange c.reduced ⊤ X.rho)
        (RationalSection.ofHom ((source.map c.reduced).order.action a) ⊤) =
      RationalSection.comp (RationalSection.ofHom ((X.reducedTarget.map c.reduced).order.action a) ⊤)
        (RationalSection.baseChange c.reduced ⊤ X.rho) at h
    have ht := congrArg (RationalSection.transportIso e.toModuleIso f.toModuleIso ⊤) h
    rw [RationalSection.transportIso_comp e.toModuleIso e.toModuleIso f.toModuleIso,
      RationalSection.transportIso_comp e.toModuleIso f.toModuleIso f.toModuleIso] at ht
    rw [RationalSection.transportIso_ofHom_of_commutes e.toModuleIso e.toModuleIso (e.hom.commutes a),
      RationalSection.transportIso_ofHom_of_commutes f.toModuleIso f.toModuleIso (f.hom.commutes a)] at ht
    exact ht
  similitude := by
    obtain ⟨m, hm⟩ := X.similitude
    exact ⟨m, (hm.baseChange c.reduced).transportIso c.sourceIso.orderIso.toModuleIso
      (c.targetIso X).orderIso.toModuleIso c.sourceIso.preserves (c.targetIso X).preserves⟩

/-- The general construction recovers ordinary pullback along Nilp morphisms. -/
theorem mapCoefficients_ofHom (j : T ⟶ U) :
    X.mapCoefficients (CoefficientChange.ofHom frame j) = X.baseChange j := rfl

/-- The extension of a coefficient square preserves isomorphisms of framed triples. -/
def Iso.mapCoefficients {X Y : PolarizedFramedAffinePoint prime π frame T} (e : Iso X Y)
    (c : CoefficientChange frame frame' T U) : Iso (X.mapCoefficients c) (Y.mapCoefficients c) where
  targetIso := e.targetIso.map c.scalar
  square := by
    let a := c.sourceIso.orderIso.toModuleIso
    let b := (c.targetIso X).orderIso.toModuleIso
    let d := (c.targetIso Y).orderIso.toModuleIso
    let f := e.targetIso.orderIso.hom.val
    let f₁ := f.map (Nilp.quotientO ℤ_[prime] T)
    let f₂ := (f.map c.scalar).map (Nilp.quotientO ℤ_[prime] U)
    have hn : d.hom.comp (f₁.map c.reduced) = f₂.comp b.hom :=
      (ModuleLaw.mapSquareIso_natural f (Nilp.quotientO ℤ_[prime] T) c.reduced c.scalar
        (Nilp.quotientO ℤ_[prime] U) c.quotientSquare).symm
    have h := congrArg (RationalSection.baseChange c.reduced ⊤) e.square
    change RationalSection.baseChange c.reduced ⊤
        (RationalSection.comp (RationalSection.ofHom f₁ ⊤) X.rho) =
      RationalSection.baseChange c.reduced ⊤ Y.rho at h
    rw [RationalSection.baseChange_comp, RationalSection.baseChange_ofHom] at h
    change RationalSection.comp (RationalSection.ofHom (f₁.map c.reduced) ⊤)
        (RationalSection.baseChange c.reduced ⊤ X.rho) =
      RationalSection.baseChange c.reduced ⊤ Y.rho at h
    have ht := congrArg (RationalSection.transportIso a d ⊤) h
    rw [RationalSection.transportIso_comp a b d,
      RationalSection.transportIso_ofHom_of_commutes b d hn] at ht
    exact ht

/-- Two coefficient changes agree with the composite up to an actual framed isometry. -/
def mapCoefficientsCompIso (c : CoefficientChange frame frame' T U)
    (d : CoefficientChange frame' frame'' U V) :
    Iso ((X.mapCoefficients c).mapCoefficients d) (X.mapCoefficients (c.comp d)) where
  targetIso := X.target.mapCompIso c.scalar d.scalar
  square := by
    let a₁ := c.sourceIso.orderIso.toModuleIso
    let a₂ := d.sourceIso.orderIso.toModuleIso
    let a₃ := (c.comp d).sourceIso.orderIso.toModuleIso
    let b₁ := (c.targetIso X).orderIso.toModuleIso
    let b₂ := (d.targetIso (X.mapCoefficients c)).orderIso.toModuleIso
    let b₃ := ((c.comp d).targetIso X).orderIso.toModuleIso
    let a₀ := mapCompIso (source (frame := frame) (T := T)).law c.reduced d.reduced
    let b₀ := mapCompIso X.reducedTarget.law c.reduced d.reduced
    let e := (X.target.mapCompIso c.scalar d.scalar).orderIso.toModuleIso.map (Nilp.quotientO ℤ_[prime] V)
    let z := RationalSection.baseChange c.reduced ⊤ X.rho
    let q := RationalSection.baseChange d.reduced ⊤ z
    let q' := RationalSection.transportIso (a₁.map d.reduced) (b₁.map d.reduced) ⊤ q
    have hz := RationalSection.baseChange_transportIso d.reduced a₁ b₁ z
    change RationalSection.baseChange d.reduced ⊤ (RationalSection.transportIso a₁ b₁ ⊤ z) = q' at hz
    have he : e.IdentityCoordinates := ModuleLaw.Iso.IdentityCoordinates.map
      (a := (X.target.mapCompIso c.scalar d.scalar).orderIso.toModuleIso) rfl _
    have ha : (a₁.map d.reduced).trans a₂ = a₀.trans a₃ := by
      apply ModuleLaw.Iso.ext_hom
      let f := a₂.hom.comp (a₁.map d.reduced).hom
      change f = (f.comp a₀.inv).comp a₀.hom
      calc
        f = f.comp (Hom.id _) := (Hom.comp_id f).symm
        _ = f.comp (a₀.inv.comp a₀.hom) := congrArg (fun g => f.comp g) a₀.inv_hom.symm
        _ = (f.comp a₀.inv).comp a₀.hom := (Hom.comp_assoc _ _ _).symm
    have hb : (b₁.map d.reduced).trans (b₂.trans e) = b₀.trans b₃ :=
      ModuleLaw.Iso.eq_of_identity
        ((ModuleLaw.Iso.IdentityCoordinates.map (a := b₁) rfl _).trans
          (ModuleLaw.Iso.IdentityCoordinates.trans (a := b₂) rfl he))
        (ModuleLaw.Iso.IdentityCoordinates.trans (a := b₀) rfl (b := b₃) rfl)
    have heq : eqToHom (coefficientOpenMap_comp_obj c.reduced d.reduced ⊤) =
        𝟙 (⊤ : Opens (PrimeSpectrum _)) := Subsingleton.elim _ _
    have hcomp : RationalSection.transportIso a₀ b₀ ⊤ q =
        RationalSection.baseChange (c.comp d).reduced ⊤ X.rho := by
      have h := RationalSection.baseChange_composite_transport c.reduced d.reduced ⊤ X.rho
      rw [heq] at h
      exact h.trans (RationalSection.restrict_id ⊤ _)
    have pullback := congrArg (fun f => RationalSection.comp (RationalSection.ofHom e.hom ⊤)
      (RationalSection.transportIso a₂ b₂ ⊤ f)) hz
    have postcompose := RationalSection.comp_transportIso a₂ b₂ e q'
    have combine := RationalSection.transportIso_trans (a₁.map d.reduced) (b₁.map d.reduced) a₂ (b₂.trans e) q
    have compare := congrArg₂ (fun a b => RationalSection.transportIso a b ⊤ q) ha hb
    have separate := (RationalSection.transportIso_trans a₀ b₀ a₃ b₃ q).symm
    have composite := congrArg (RationalSection.transportIso a₃ b₃ ⊤) hcomp
    exact pullback.trans (postcompose.trans (combine.trans (compare.trans (separate.trans composite))))

/-- The extension descends to the quotient by actual framed isomorphisms. -/
def IsomorphismClass.mapCoefficients (q : IsomorphismClass (frame := frame) (T := T))
    (c : CoefficientChange frame frame' T U) : IsomorphismClass (frame := frame') (T := U) := by
  refine Quotient.map (fun X : PolarizedFramedAffinePoint prime π frame T => X.mapCoefficients c) ?_ q
  intro X Y h
  change Nonempty (Iso X Y) at h
  exact h.map (fun e => e.mapCoefficients c)

/-- A class map along a Nilp morphism is the existing class pullback. -/
theorem IsomorphismClass.mapCoefficients_ofHom
    (q : IsomorphismClass (frame := frame) (T := T)) (j : T ⟶ U) :
    q.mapCoefficients (CoefficientChange.ofHom frame j) = q.baseChange j := by
  induction q using Quotient.inductionOn with
  | h X => exact congrArg (Quotient.mk _) (X.mapCoefficients_ofHom j)

/-- Class maps preserve the composite of coefficient squares. -/
theorem IsomorphismClass.mapCoefficients_comp
    (q : IsomorphismClass (frame := frame) (T := T))
    (c : CoefficientChange frame frame' T U) (d : CoefficientChange frame' frame'' U V) :
    (q.mapCoefficients c).mapCoefficients d = q.mapCoefficients (c.comp d) := by
  induction q using Quotient.inductionOn with
  | h X => exact Quotient.sound ⟨X.mapCoefficientsCompIso c d⟩

end Langlands.FormalGroup.PolarizedFramedAffinePoint
