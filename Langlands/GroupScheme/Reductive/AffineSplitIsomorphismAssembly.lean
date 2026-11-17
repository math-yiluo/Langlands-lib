import Langlands.GroupScheme.Reductive.AffineSplitWeylRelations
import Langlands.GroupScheme.Reductive.AffineSplitTorusCompatibility
import Langlands.GroupScheme.Reductive.AffineSplitIsomorphismTheoremStatement

/-! # Affine split isomorphism from normalized root families and local relations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- Weyl-normalized simple root families and the two local relation statements
produce an isomorphism preserving a common coordinate torus over any ring. -/
theorem exists_iso_comp_torus_of_weylRelations
    (h2 : LocalSplitWeylCommutatorStatement.{u}) (h3 : LocalSplitWeylNegSimpleStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i')
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (hP' : IsFibrewiseRootDatumOf I H i' P)
    (b : P.Base) (W : ∀ α, SimpleWord P b α) (hD : IsDescendingWords P b W)
    (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H))
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (hu' : ∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) ∧
      IsRootParametrization i' (P.root (P.reflectionPerm a a)) (u' (P.reflectionPerm a a)))
    (hw' : ∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a)) :
    ∃ ψ : G ≅ H, i ≫ ψ.hom = i' := by
  classical
  have : Finite J := hP.finite
  let : Fintype J := Fintype.ofFinite J
  let neg := (Finite.equivFin {α // ¬ b.IsPos α}).symm
  obtain ⟨pos, hmono⟩ :=
    exists_equiv_monotone (fun α : {α // b.IsPos α} => b.height (α : J))
  obtain ⟨ψ, hψ⟩ := localSplitCommutatorLawIsomorphism R I J G H hG hH i i' hmax hmax' P hP hP'
    b W hD.1 u u' (fun a ha => (hu a ha).1) hw (fun a ha => (hu' a ha).1) hw'
    _ _ neg pos hmono
    (AffineSplitWeylRelations.commutatorRelations_of_local
      h2 hG hH hi hi' hmax hmax' hP hP' W hD u u' hu hw hu' hw' pos hmono)
    (AffineSplitWeylRelations.negSimpleRelations_of_local
      h3 hG hH hi hi' hmax hmax' hP hP' W hD u u' hu hw hu' hw' neg pos hmono)
  exact ⟨ψ, torus_comp_of_cellMap_comp ψ.hom hψ⟩

end LocalSplitCell

open LocalSplitCell

/-- The affine split Isomorphism Theorem reduces to normalized root families,
local relations and transport of free root spaces to a common coordinate torus. -/
def AffineSplitWeylRelationsReductionStatement : Prop :=
  ∀
    (_h1 :
      ∀ {R : Type u} [CommRing R]
        {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
        (_hG : IsReductive G) {I : Type u} [Fintype I] [DecidableEq I]
        (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
        IsClosedSubgroup i →
        IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
        ∀ {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)},
        IsFibrewiseRootDatumOf I G i P →
        (∀ α : J, Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
          CommRingCat.of R)) →
        ∀ b : P.Base, ∃ u : J → (Ga R ⟶ G),
          (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
            IsRootParametrization i (P.root (P.reflectionPerm a a))
              (u (P.reflectionPerm a a))) ∧
          ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (_h2 : LocalSplitWeylCommutatorStatement.{u}) (_h3 : LocalSplitWeylNegSimpleStatement.{u})
    (_htransport :
      ∀ {R : Type u} [CommRing R] {I I' : Type u} [Fintype I] [Fintype I']
        [DecidableEq I] [DecidableEq I']
        {H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]
        {J J' : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
        {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
        (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
        (e : RootPairing.Equiv P Q),
        (∀ α : J', Nonempty (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R]
          CommRingCat.of R)) →
        ∀ α : J, Nonempty
          (splitTorus.exponentWeightSpace I H (precompTorus e.weightEquiv i') (P.root α) ≃ₗ[
            CommRingCat.of R] CommRingCat.of R)),
    AffineSplitIsomorphismTheoremStatement.{u}

/-- Assemble the exact affine target from the four explicit reduction inputs. -/
theorem affineSplitIsomorphismTheorem_of_weylRelations :
    AffineSplitWeylRelationsReductionStatement.{u} := by
  intro h1 h2 h3 htransport R _ G H hG hH I I' _ _ i i' J J' P Q hi hmax hP hfree hi' hmax' hQ
    hfree' f
  classical
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  have : Finite J := hP.finite
  have : P.IsReduced := hP.isReduced
  obtain ⟨b⟩ := Langlands.LinearAlgebra.RootDatumBase.nonempty_base P
  let j := precompTorus f.symm.weightEquiv i'
  have hj : IsClosedSubgroup j := isClosedSubgroup_precompTorus f.symm.weightEquiv hi'
  have hmaxj : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) j :=
    isFibrewiseMaximalTorus_precompTorus f.symm.weightEquiv hmax'
  have hPj : IsFibrewiseRootDatumOf I H j P :=
    isFibrewiseRootDatumOf_precompTorus hP hQ f.symm
  obtain ⟨u, hu, hw⟩ := h1 hG i hi hmax hP hfree b
  obtain ⟨u', hu', hw'⟩ := h1 hH j hj hmaxj hPj (htransport i' f.symm hfree') b
  obtain ⟨φ, hφ⟩ := exists_iso_comp_torus_of_weylRelations h2 h3 hG hH hi hj hmax hmaxj
    hP hPj b (descWord P b) (isDescendingWords_descWord P b) u u' hu hw hu' hw'
  refine ⟨φ, exponentEquivGroupIso _ f.symm.weightEquiv, hφ, ?_⟩
  intro U x m
  have h := splitTorus.pointsEquiv_exponentEquivGroupIso
    (Spec (CommRingCat.of R)) f.symm.weightEquiv U x m
  have hfm : f.symm.weightEquiv.symm m = f.weightMap m := by
    apply f.symm.weightEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    change m = f.weightEquiv.symm (f.weightEquiv m)
    exact (f.weightEquiv.symm_apply_apply m).symm
  rw [hfm] at h
  exact h

end Langlands.GroupScheme
