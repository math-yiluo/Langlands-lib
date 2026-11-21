import Langlands.AlgebraicGeometry.ProjectiveSpace.BoundedHomogeneousEquations
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace
import Langlands.AlgebraicGeometry.ULiftIntAlgebra
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower

/-! # A uniform equation bound on local-ring tests of a noetherian family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.RelativeProjectiveSpace

open Langlands.AlgebraicGeometry ProjectiveSpace

attribute [local instance] ULiftInt.algebra

/-- The polynomial-Proj model and the relative pullback model of projective space over an
actual affine base are canonically identified, with their given projections. -/
def polynomialIsoSpec (B : Type u) [CommRing B] (m : ℕ) :
    ProjectiveSpace B m ≅ RelativeProjectiveSpace (Spec (CommRingCat.of B)) m where
  hom := lift m (projectiveSpaceToSpec B m) (baseChangeMap (ULift.{u} ℤ) B m)
  inv := (baseChangeMap_isPullback (ULift.{u} ℤ) B m).lift (toIntegral _ m) (toBase _ m)
    (specULiftZIsTerminal.hom_ext _ _)
  hom_inv_id := by
    apply (baseChangeMap_isPullback (ULift.{u} ℤ) B m).hom_ext
    · rw [Category.assoc, IsPullback.lift_fst, lift_toIntegral, Category.id_comp]
    · rw [Category.assoc, IsPullback.lift_snd, lift_toBase, Category.id_comp]
  inv_hom_id := by
    apply hom_ext
    · rw [Category.assoc, lift_toBase, IsPullback.lift_snd, Category.id_comp]
    · rw [Category.assoc, lift_toIntegral, IsPullback.lift_fst, Category.id_comp]

@[reassoc (attr := simp)]
lemma polynomialIsoSpec_hom_toBase (B : Type u) [CommRing B] (m : ℕ) :
    (polynomialIsoSpec B m).hom ≫ toBase _ m = projectiveSpaceToSpec B m :=
  lift_toBase _ _ _

@[reassoc (attr := simp)]
lemma polynomialIsoSpec_hom_toIntegral (B : Type u) [CommRing B] (m : ℕ) :
    (polynomialIsoSpec B m).hom ≫ toIntegral _ m = baseChangeMap (ULift.{u} ℤ) B m :=
  lift_toIntegral _ _ _

set_option maxHeartbeats 600000 in
/-- Extending coefficients in the polynomial-Proj model agrees with changing the affine
base in the relative model. -/
lemma polynomialIsoSpec_natural (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (m : ℕ) :
    ProjSpace.map B C m ≫ (polynomialIsoSpec B m).hom =
      (polynomialIsoSpec C m).hom ≫ map m (Spec.map (CommRingCat.ofHom (algebraMap B C))) := by
  apply hom_ext
  · simpa only [Category.assoc, polynomialIsoSpec_hom_toBase, map_toBase,
      polynomialIsoSpec_hom_toBase_assoc, baseChangeMap] using (baseChangeMap_isPullback B C m).w
  · simp only [Category.assoc, polynomialIsoSpec_hom_toIntegral, map_toIntegral, baseChangeMap]
    have hTower : @IsScalarTower (ULift.{u} ℤ) B C (ULiftInt.algebra B).toSMul
        (‹Algebra B C›).toSMul (ULiftInt.algebra C).toSMul := by
      refine @IsScalarTower.of_algebraMap_eq (ULift.{u} ℤ) B C _ _ _ (ULiftInt.algebra B)
        ‹Algebra B C› (ULiftInt.algebra C) ?_
      intro r
      change (r.down : C) = algebraMap B C (r.down : B)
      exact (map_intCast (algebraMap B C) r.down).symm
    open P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower in
    have hc := @P2mK4G.map_comp_map (ULift.{u} ℤ) B C inferInstance ‹CommRing B› ‹CommRing C›
      (ULiftInt.algebra B) ‹Algebra B C› (ULiftInt.algebra C) hTower m
    exact hc

/-- For an ideal sheaf on relative projective space over a noetherian scheme, there is a
single equation degree bound for its pullbacks to polynomial projective spaces over all
local rings, along all maps of their spectra to the base. -/
theorem exists_uniformBoundedHomogeneousEquations {T : Scheme.{u}} [IsNoetherian T]
    (m : ℕ) (W : (RelativeProjectiveSpace T m).IdealSheafData) :
    ∃ D : ℕ, ∀ (A : Type u) [CommRing A] [IsLocalRing A] (x : Spec (CommRingCat.of A) ⟶ T),
      HasBoundedHomogeneousEquations (W.comap ((polynomialIsoSpec A m).hom ≫ map m x)) D := by
  classical
  let C := T.affineCover.finiteSubcover
  have (i : C.I₀) : IsAffine (C.X i) := by
    rw [T.affineCover.finiteSubcover_X]
    apply Scheme.isAffine_affineCover
  let B (i : C.I₀) : CommRingCat.{u} := Γ(C.X i, ⊤)
  let j (i : C.I₀) : Spec (B i) ⟶ T := (C.X i).isoSpec.inv ≫ C.f i
  let I (i : C.I₀) := W.comap ((polynomialIsoSpec (B i) m).hom ≫ map m (j i))
  have hex (i : C.I₀) : ∃ D, HasBoundedHomogeneousEquations (I i) D := by
    have : IsNoetherianRing (B i) := (isLocallyNoetherian_iff_of_affine_openCover C).mp
      (inferInstanceAs (IsLocallyNoetherian T)) i
    exact exists_boundedHomogeneousEquations (I i)
  choose d hd using hex
  let := Fintype.ofFinite C.I₀
  refine ⟨Finset.univ.sup d, fun A _ _ x => ?_⟩
  let i := C.idx (x (IsLocalRing.closedPoint A))
  have hrange : Set.range x ⊆ (C.f i).opensRange := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map x.continuous).mem_open
      (C.f i).opensRange.2 (C.covers _)
  let f := IsOpenImmersion.lift (C.f i) x hrange
  let r : Spec (CommRingCat.of A) ⟶ Spec (B i) := f ≫ (C.X i).isoSpec.hom
  have hr : r ≫ j i = x := by
    simp only [r, j, Category.assoc, Iso.hom_inv_id_assoc, f, IsOpenImmersion.lift_fac]
  let := (Spec.preimage r).hom.toAlgebra
  have hk : Spec.map (CommRingCat.ofHom (algebraMap (B i) A)) = r := Spec.map_preimage r
  have hb := HasBoundedHomogeneousEquations.comap_map (B i) m A (hd i)
  simp only [I, ← Scheme.IdealSheafData.comap_comp] at hb
  rw [← Category.assoc, polynomialIsoSpec_natural, hk, Category.assoc, ← map_comp, hr] at hb
  exact hb.mono (Finset.le_sup (f := d) (Finset.mem_univ i))

end Langlands.AlgebraicGeometry.RelativeProjectiveSpace
