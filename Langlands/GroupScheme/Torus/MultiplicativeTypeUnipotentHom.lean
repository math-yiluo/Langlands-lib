import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Unipotent.TorusHom
import Langlands.GroupScheme.FactoredKernel
import Langlands.GroupScheme.Absolute.ParabolicTransport

/-! # Multiplicative-type subgroups of unipotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {D U E G : GroupScheme (Spec (CommRingCat.of k))}

/-- A homomorphism from any diagonalizable group to an affine unipotent group is zero. -/
theorem Diagonalizable.hom_eq_zero_of_isUnipotent
    (Λ : Type u) [AddCommGroup Λ] [IsAffine U.X.left]
    (hU : IsUnipotent U)
    (f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ U) : f = 0 := by
  let eU := AffineCoordinates.groupSchemeIso U
  have hU' : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)) := IsUnipotent.of_iso eU hU
  have h0 := Unipotent.diagonalizable_hom_eq_zero Λ (AffineCoordinates.corepresentation U)
    (Unipotent.oneMemStable_of_isUnipotent _ hU') (f ≫ eU.inv)
  calc f = (f ≫ eU.inv) ≫ eU.hom := by simp
       _ = 0 := by erw [h0, zero_comp]

/-- Every homomorphism from a group of multiplicative type to an affine unipotent group
is zero, including when the multiplicative-type group is not smooth. -/
theorem IsMultiplicativeType.hom_eq_zero_of_isUnipotent [IsAffineHom U.X.hom]
    (hD : IsMultiplicativeType D) (hU : IsUnipotent U) (f : D ⟶ U) : f = 0 := by
  obtain ⟨K, _, _, Λ, _, _, ⟨eD⟩⟩ := hD
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  have : IsAffineHom (B.obj U).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd U.X.hom b))
  have : IsAffine (B.obj U).X.left := isAffine_of_isAffineHom (B.obj U).X.hom
  have h0 := Diagonalizable.hom_eq_zero_of_isUnipotent Λ (hU.baseChange (K := K))
    (eD.inv ≫ B.map f)
  have h : B.map f = 0 := by
    calc B.map f = eD.hom ≫ (eD.inv ≫ B.map f) := by simp
         _ = 0 := by rw [h0, comp_zero]
  have := GaloisCocharacterDescent.faithful_algebraPullback k K
  apply (Grp.forget _).map_injective
  change f.hom.hom = (1 : D.X ⟶ U.X)
  apply (Over.pullback b).map_injective
  rw [Functor.map_one]
  exact congrArg (fun j => j.hom.hom) h

/-- The unique homomorphism from a multiplicative-type group to an affine unipotent
group identifies its hom-set with the one-point type. -/
def IsMultiplicativeType.unipotentHomEquiv [IsAffineHom U.X.hom]
    (hD : IsMultiplicativeType D) (hU : IsUnipotent U) : (D ⟶ U) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := 0
  left_inv f := (hD.hom_eq_zero_of_isUnipotent hU f).symm
  right_inv _ := Subsingleton.elim _ _

/-- A closed unipotent subgroup contained in a multiplicative-type closed subgroup is
trivial on every test scheme. -/
theorem IsUnipotent.range_eq_bot_of_range_le_isMultiplicativeType
    [IsAffineHom U.X.hom] (hU : IsUnipotent U) (hD : IsMultiplicativeType D)
    (f : U ⟶ E) (i : D ⟶ E) (hf : IsClosedSubgroup f)
    (hi : IsClosedSubgroup i) (h : SubgroupFunctor.range f ≤ SubgroupFunctor.range i) :
    SubgroupFunctor.range f = ⊥ := by
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let g := SubgroupFunctor.factorOfRangeLE h
  have hg : g ≫ i = f := SubgroupFunctor.factorOfRangeLE_comp h
  have hgc : IsClosedSubgroup g := by
    have : IsClosedImmersion (g.hom.hom.left ≫ i.hom.hom.left) := by
      change IsClosedImmersion (g ≫ i).hom.hom.left
      rw [hg]
      exact hf
    exact IsClosedImmersion.of_comp_isClosedImmersion g.hom.hom.left i.hom.hom.left
  have hUmt : IsMultiplicativeType U := hD.of_isClosedSubgroup g hgc
  have hid : (𝟙 U : U ⟶ U) = 0 := hUmt.hom_eq_zero_of_isUnipotent hU (𝟙 U)
  have hf0 : f = 0 := by
    calc f = (𝟙 U : U ⟶ U) ≫ f := by simp
         _ = 0 := by rw [hid, zero_comp]
  rw [hf0, SubgroupFunctor.range_zero]

/-- Restricting a homomorphism to a closed subgroup preserves multiplicative type of
its full scheme-theoretic kernel. -/
theorem IsMultiplicativeType.kernel_comp_of_isClosedSubgroup
    (q : E ⟶ G) (hD : IsMultiplicativeType (kernel q)) (i : D ⟶ E)
    (hi : IsClosedSubgroup i) : IsMultiplicativeType (kernel (i ≫ q)) := by
  let m := FactoredKernel.map (i ≫ q) i q rfl
  have hm : IsClosedSubgroup m :=
    MorphismProperty.of_isPullback
      (P := @IsClosedImmersion) (FactoredKernel.isPullback_scheme (i ≫ q) i q rfl) hi
  exact hD.of_isClosedSubgroup m hm

end Langlands.GroupScheme
