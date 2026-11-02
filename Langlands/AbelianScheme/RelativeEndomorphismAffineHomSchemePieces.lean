import Langlands.AbelianScheme.RelativeEndomorphismAffineHomScheme
import Langlands.AbelianScheme.RelativeEndomorphismOfAffineHomSchemeGluing
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial
import Langlands.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections

/-! # The affine-test Hom scheme of an H-projective abelian scheme -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry Opposite NeronModelInfra GoodReductionJacobian
open Langlands.GroupScheme.Cartier
open scoped CategoryTheory.MonObj CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.AbelianScheme.AffineHomSchemePieces

universe u

variable {R : Type u} [CommRing R] (A : Langlands.AbelianScheme (Spec (CommRingCat.of R)))

/-! ### The FLT data of an abelian scheme -/

instance grpObjOverMk : GrpObj (Over.mk A.X.hom) := inferInstanceAs (GrpObj A.X)

instance isCommMonObjOverMk : IsCommMonObj (Over.mk A.X.hom) :=
  inferInstanceAs (IsCommMonObj A.X)

/-- The FLT relative group law given by the group structure of `A`. -/
abbrev groupLaw : RelativeGroupLaw R A.X.hom := relativeGroupLawOfGrpObj R A.X.hom

theorem groupLaw_isCommutative : (groupLaw A).IsCommutative := by
  intro T t x y
  simp only [relativeGroupLawOfGrpObj_mul]
  rw [mul_comm]

theorem propertyBundle : AbelianSchemePropertyBundle R A.X.hom where
  smooth := inferInstance
  proper := inferInstance
  connectedFibres s := A.X.hom.isConnected_preimage_singleton s
  hasGroupLaw := ⟨groupLaw A⟩

/-- An H-projective abelian scheme carries an invertible module whose sections give a closed
immersion into projective space, in the sense of FLT. -/
theorem exists_lineBundle (h : Langlands.AlgebraicGeometry.IsHProjective A.X.hom) :
    ∃ L : A.X.left.Modules, Scheme.Modules.IsInvertible L ∧
      Scheme.Modules.ClosedImmersionBySections L A.X.hom := by
  obtain ⟨n, i, hi, hcomp⟩ := h
  obtain ⟨L, 𝔓, h𝔓, hloc⟩ :=
    _root_.AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial
      (A := R) (n := n) i
  refine ⟨L, ⟨hloc⟩, ?_⟩
  have hf : i ≫ _root_.AlgebraicGeometry.ProjSpace.π R n = A.X.hom := hcomp
  rw [← hf]
  exact ⟨n, 𝔓, by rw [h𝔓]; exact hi⟩

/-! ### Relative homomorphisms and FLT homomorphisms -/

/-- FLT's condition that a morphism `A_{S'} ⟶ A` over `Spec R` is a homomorphism. -/
def IsFLTHom {S' : Type u} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (φ : pullback A.X.hom s ⟶ A.X.left) (hφ : φ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s) :
    Prop :=
  ∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) A.X.hom),
    pullback.lift ((groupLaw A).mul (t' ≫ s) P Q).1 t' ((groupLaw A).mul (t' ≫ s) P Q).2 ≫ φ =
      ((groupLaw A).mul (t' ≫ s)
        ⟨pullback.lift P.1 t' P.2 ≫ φ, by
          rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
        ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by
          rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1

theorem isFLTHom_iff {S' : Type u} [CommRing S']
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (φ : pullback A.X.hom s ⟶ A.X.left) (hφ : φ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s) :
    IsFLTHom A s φ hφ ↔
      IsPtMul (G := A.toCommGroupScheme) (H := A.toCommGroupScheme) (T := Over.mk s) φ hφ := by
  constructor
  · intro h Z x₀ P Q
    apply Over.OverMorphism.ext
    exact h Z x₀ (overHomToSchemeHomOver (P : Over.mk (x₀ ≫ s) ⟶ Over.mk A.X.hom))
      (overHomToSchemeHomOver (Q : Over.mk (x₀ ≫ s) ⟶ Over.mk A.X.hom))
  · intro h T t' P Q
    exact congrArg CommaMorphism.left (h t' (schemeHomOverToOverHom P : Over.mk (t' ≫ s) ⟶ A.X)
      (schemeHomOverToOverHom Q : Over.mk (t' ≫ s) ⟶ A.X))

theorem isFLTHom_fstMap {S' : Type u} [CommRing S']
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (χ : RelativeHom A.toCommGroupScheme A.toCommGroupScheme (Over.mk s)) :
    IsFLTHom A s (fstMap χ) (fstMap_hom χ) :=
  (isFLTHom_iff A s _ _).mpr (isPtMul_fstMap χ)

/-! ### Points of the Hom scheme over spectra -/

section Points

variable {A} {H : Scheme.{u}} {πH : H ⟶ Spec (CommRingCat.of R)}
  (pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (φ : pullback A.X.hom s ⟶ A.X.left), φ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s →
      SchemeHomOver s πH)

theorem pt_congr {S' : Type u} [CommRing S']
    {s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)}
    {φ₁ φ₂ : pullback A.X.hom s ⟶ A.X.left} (h₁ : φ₁ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s)
    (h₂ : φ₂ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s) (h : φ₁ = φ₂) :
    pt S' s φ₁ h₁ = pt S' s φ₂ h₂ := by
  subst h; rfl

/-- The point of the Hom scheme given by a relative homomorphism over `Spec S'`. -/
def homPt {S' : Type u} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (χ : RelativeHom A.toCommGroupScheme A.toCommGroupScheme (Over.mk s)) :
    SchemeHomOver s πH :=
  pt S' s (fstMap χ) (fstMap_hom χ)

/-- FLT's naturality of `pt` along ring maps. -/
def PtNat : Prop :=
  ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (φ : pullback A.X.hom s ⟶ A.X.left) (hφ : φ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s),
    (pt S'' s''
        (pullback.lift (pullback.fst A.X.hom s'')
            (pullback.snd A.X.hom s'' ≫ Spec.map (CommRingCat.ofHom ψ))
            (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
        (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc,
          hs])).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1

/-- FLT's surjectivity of `pt` on homomorphisms. -/
def PtSurj : Prop :=
  ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver s πH),
    ∃ (φ : pullback A.X.hom s ⟶ A.X.left) (hφ : φ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s),
      IsFLTHom A s φ hφ ∧ pt S' s φ hφ = x

/-- FLT's injectivity of `pt` on homomorphisms. -/
def PtInj : Prop :=
  ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (φ φ' : pullback A.X.hom s ⟶ A.X.left) (hφ : φ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s)
    (hφ' : φ' ≫ A.X.hom = pullback.snd A.X.hom s ≫ s),
    IsFLTHom A s φ hφ → IsFLTHom A s φ' hφ' → pt S' s φ hφ = pt S' s φ' hφ' → φ = φ'

variable {pt}

theorem homPt_injective (hinj : PtInj pt)
    {S' : Type u} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (homPt pt s) := fun χ χ' h =>
  relativeHom_ext χ χ' (hinj S' s _ _ _ _ (isFLTHom_fstMap A s χ) (isFLTHom_fstMap A s χ') h)

theorem homPt_surjective (hsurj : PtSurj pt)
    {S' : Type u} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) :
    Function.Surjective (homPt pt s) := by
  intro x
  obtain ⟨φ, hφ, hhom, rfl⟩ := hsurj S' s x
  exact ⟨ofFstMap (G := A.toCommGroupScheme) (H := A.toCommGroupScheme) (T := Over.mk s) φ hφ
    ((isFLTHom_iff A s φ hφ).mp hhom), pt_congr pt _ _ (fstMap_ofFstMap _ _ _)⟩

theorem homPt_restrict (hnat : PtNat pt)
    {S' S'' : Type u} [CommRing S'] [CommRing S'']
    {s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)}
    {s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R)} (c : Over.mk s'' ⟶ Over.mk s)
    (χ : RelativeHom A.toCommGroupScheme A.toCommGroupScheme (Over.mk s)) :
    (homPt pt s'' (restrict _ _ c χ)).1 = c.left ≫ (homPt pt s χ).1 := by
  let ψ := Spec.preimage c.left
  have hψ : Spec.map (CommRingCat.ofHom ψ.hom) = c.left := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hs : Spec.map (CommRingCat.ofHom ψ.hom) ≫ s = s'' := by
    rw [hψ]; exact Over.w c
  have hn := hnat S' S'' ψ.hom s s'' hs (fstMap χ) (fstMap_hom χ)
  show (pt S'' s'' (fstMap (restrict _ _ c χ)) (fstMap_hom _)).1 =
    c.left ≫ (pt S' s (fstMap χ) (fstMap_hom χ)).1
  rw [← hψ, ← hn]
  refine congrArg Subtype.val (pt_congr pt _ _ ?_)
  rw [fstMap_restrict]
  refine congrArg (· ≫ fstMap χ) ?_
  apply pullback.hom_ext
  · exact (baseChangeProj_fst A.toCommGroupScheme c).trans (pullback.lift_fst _ _ _).symm
  · refine (baseChangeProj_snd A.toCommGroupScheme c).trans
      (Eq.trans ?_ (pullback.lift_snd _ _ _).symm)
    rw [hψ]
    rfl

end Points

/-! ### Affine test schemes -/

section Affine

variable (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left]

/-- The coordinate ring of an affine test scheme. -/
abbrev coordRing : Type u := Γ(T.left, ⊤)

/-- An affine test scheme is the spectrum of its coordinate ring. -/
abbrev isoSpec : T.left ≅ Spec (CommRingCat.of (coordRing T)) := T.left.isoSpec

/-- The structure morphism of the spectrum of the coordinate ring. -/
abbrev specHom : Spec (CommRingCat.of (coordRing T)) ⟶ Spec (CommRingCat.of R) :=
  (isoSpec T).inv ≫ T.hom

/-- The isomorphism from an affine test scheme to the spectrum of its coordinate ring. -/
def toSpec : T ⟶ Over.mk (specHom T) := Over.homMk (isoSpec T).hom (by simp [specHom])

/-- The isomorphism from the spectrum of the coordinate ring to the affine test scheme. -/
def ofSpec : Over.mk (specHom T) ⟶ T := Over.homMk (isoSpec T).inv rfl

@[reassoc (attr := simp)]
lemma toSpec_ofSpec : toSpec T ≫ ofSpec T = 𝟙 T := by
  ext; simp [toSpec, ofSpec]

@[reassoc (attr := simp)]
lemma ofSpec_toSpec : ofSpec T ≫ toSpec T = 𝟙 _ := by
  ext; simp [toSpec, ofSpec]

/-- Restriction to the spectrum of the coordinate ring, as a bijection. -/
def restrictEquiv : RelativeHom A.toCommGroupScheme A.toCommGroupScheme T ≃
    RelativeHom A.toCommGroupScheme A.toCommGroupScheme (Over.mk (specHom T)) where
  toFun := restrict _ _ (ofSpec T)
  invFun := restrict _ _ (toSpec T)
  left_inv χ := by
    rw [← restrict_comp, toSpec_ofSpec, restrict_id]
  right_inv χ := by
    rw [← restrict_comp, ofSpec_toSpec, restrict_id]

variable {H : Scheme.{u}} (πH : H ⟶ Spec (CommRingCat.of R))

/-- Points over the spectrum of the coordinate ring are morphisms from the test scheme. -/
def pointEquiv : SchemeHomOver (specHom T) πH ≃ (T ⟶ Over.mk πH) where
  toFun x := toSpec T ≫ Over.homMk x.1 x.2
  invFun g := ⟨(ofSpec T ≫ g).left, Over.w (ofSpec T ≫ g)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv g := by
    ext
    simp [toSpec, ofSpec]

end Affine

/-! ### The natural bijection on affine test schemes -/

section Represent

variable {A} {H : Scheme.{u}} {πH : H ⟶ Spec (CommRingCat.of R)}
  {pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
    (φ : pullback A.X.hom s ⟶ A.X.left), φ ≫ A.X.hom = pullback.snd A.X.hom s ≫ s →
      SchemeHomOver s πH}
  (hsurj : PtSurj pt) (hinj : PtInj pt)

/-- Relative homomorphisms over an affine test scheme `T` are the morphisms `T ⟶ H`. -/
def homEquiv (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    RelativeHom A.toCommGroupScheme A.toCommGroupScheme T ≃ (T ⟶ Over.mk πH) :=
  ((restrictEquiv A T).trans (Equiv.ofBijective (homPt pt (specHom T))
    ⟨homPt_injective hinj _, homPt_surjective hsurj _⟩)).trans (pointEquiv T πH)

theorem homEquiv_left (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left]
    (χ : RelativeHom A.toCommGroupScheme A.toCommGroupScheme T) :
    (homEquiv hsurj hinj T χ).left =
      (isoSpec T).hom ≫ (homPt pt (specHom T) (restrict _ _ (ofSpec T) χ)).1 := by
  simp [homEquiv, restrictEquiv, pointEquiv, toSpec]

theorem homEquiv_restrict (hnat : PtNat pt) {T T' : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] [IsAffine T'.left] (b : T' ⟶ T)
    (χ : RelativeHom A.toCommGroupScheme A.toCommGroupScheme T) :
    homEquiv hsurj hinj T' (restrict _ _ b χ) = b ≫ homEquiv hsurj hinj T χ := by
  have hc : (ofSpec T' ≫ b ≫ toSpec T) ≫ ofSpec T = ofSpec T' ≫ b := by simp
  have h1 : restrict _ _ (ofSpec T') (restrict A.toCommGroupScheme A.toCommGroupScheme b χ) =
      restrict _ _ (ofSpec T' ≫ b ≫ toSpec T)
        (restrict A.toCommGroupScheme A.toCommGroupScheme (ofSpec T) χ) := by
    rw [← restrict_comp, ← restrict_comp, hc]
  apply Over.OverMorphism.ext
  rw [homEquiv_left, Over.comp_left, homEquiv_left, h1, homPt_restrict hnat]
  simp [toSpec, ofSpec]

/-- The relative endomorphism functor of `A`, restricted to affine test schemes, is represented
by `H` over `Spec R`. -/
def natIso (hnat : PtNat pt) (hsurj : PtSurj pt) (hinj : PtInj pt) :
    ((ObjectProperty.ι (fun T : Over (Spec (CommRingCat.of R)) => IsAffine T.left)).op ⋙
        relativeHomFunctor A.toCommGroupScheme A.toCommGroupScheme ⋙ forget AddCommGrpCat.{u}) ≅
      ((ObjectProperty.ι (fun T : Over (Spec (CommRingCat.of R)) => IsAffine T.left)).op ⋙
        yoneda.obj (Over.mk πH)) :=
  NatIso.ofComponents
    (fun T => haveI := T.unop.property; (homEquiv hsurj hinj T.unop.obj).toIso)
    (fun {T T'} b => by
      have := T.unop.property
      have := T'.unop.property
      ext χ
      exact homEquiv_restrict hsurj hinj hnat b.unop.hom χ)

end Represent

/-! ### The affine-test Hom scheme with its pieces -/

/-- **The affine-test Hom scheme of an H-projective abelian scheme.** For an H-projective
abelian scheme `A` over a noetherian ring `R`, the relative endomorphism functor of `A` on affine
test schemes is represented by a scheme `H` over `Spec R`, separated, locally of finite type and
formally unramified, which is the disjoint union of closed open subschemes quasi-compact over
`Spec R`. -/
theorem affineHomSchemePieces : AffineHomSchemePiecesStatement.{u} := by
  intro R _ _ A hproj
  obtain ⟨L, hL₁, hL₂⟩ := exists_lineBundle A hproj
  obtain ⟨H, πH, pt, hnat, hsurj, hinj, hsep, hlft, -, hfu, U, hdisj, hcov, hU⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
      R A.X.hom A.X.hom (groupLaw A) (groupLaw A) (groupLaw_isCommutative A)
      (groupLaw_isCommutative A) (propertyBundle A) (propertyBundle A) L hL₁ hL₂ L hL₁ hL₂
  refine ⟨Over.mk πH, hsep, hlft, hfu, ⟨natIso (pt := pt) hnat hsurj hinj⟩,
    ULift.{u} (Polynomial ℚ), fun P => U P.down, fun P => (hU P.down).1,
    fun P => (hU P.down).2.1, fun P Q h => hdisj fun h' => h (ULift.ext _ _ h'), ?_⟩
  rw [← hcov]
  exact Equiv.ulift.surjective.iSup_comp U

end Langlands.AbelianScheme.AffineHomSchemePieces
