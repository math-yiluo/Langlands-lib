import Langlands.GroupScheme.OddOrthogonalMatrix.ConnectedGenerators

/-! # Trivial unipotent radical of the actual odd identity component -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix

variable {l : Type} [Fintype l] [DecidableEq l] (K : Type u) [Field K]

local notation "𝐆" => groupScheme l K

/-- Every smooth connected unipotent normal subgroup of the actual odd
identity component is trivial, in every characteristic. -/
theorem hasTrivialUnipotentRadical_identityComponent [Nontrivial l] :
    HasTrivialUnipotentRadical (identityComponent 𝐆) := by
  intro H i _ _ _ hU hN
  let j := i ≫ identityComponentι 𝐆
  have hconj (T : Over (Spec (CommRingCat.of K))) (c : T ⟶ 𝐆.X)
      (hc : c ∈ (SubgroupFunctor.range (identityComponentι 𝐆)).carrier T)
      (h : T ⟶ H.X) : ∃ h' : T ⟶ H.X,
        h' ≫ j.hom.hom = c⁻¹ * (h ≫ j.hom.hom) * c := by
    obtain ⟨c₀, hc₀⟩ := SubgroupFunctor.mem_range.mp hc
    obtain ⟨h', hh'⟩ := SubgroupFunctor.mem_range.mp
      (hN T c₀⁻¹ (h ≫ i.hom.hom) trivial (SubgroupFunctor.mem_range.mpr ⟨h, rfl⟩))
    refine ⟨h', ?_⟩
    dsimp only [j]
    rw [Grp.comp_hom_hom, ← Category.assoc, hh', inv_inv, MonObj.mul_comp,
      MonObj.mul_comp, GrpObj.inv_comp, hc₀, Category.assoc]
  let W := MatrixRepresentation.fixedSubmodule (j ≫ inclusion K)
  obtain ⟨v, hv0, hv⟩ := hU (Index l) (j ≫ inclusion K)
  have hW : W ≠ ⊥ := (Submodule.ne_bot_iff W).mpr ⟨v, hv, hv0⟩
  have hEven (g : OrthogonalMatrix.orthogonalGroup l K)
      (hg : ∀ T : Over (Spec (CommRingCat.of K)), OrthogonalMatrix.constantPoint T g ∈
        (SubgroupFunctor.range (identityComponentι
          (OrthogonalMatrix.groupScheme l (CommRingCat.of K)))).carrier T)
      (w : Index l → K) (hw : w ∈ W) : evenBlock g *ᵥ w ∈ W := by
    exact mulVec_mem_fixedSubmodule K j (evenUnits g) (fun T => evenConstantPoint K T g)
      (fun T => pointMatrix_evenConstantPoint K T g)
      (fun T h => hconj T _ (evenConstantPoint_mem K T g (hg T)) h) hw
  have hShort (a : l ⊕ l) (w : Index l → K) (hw : w ∈ W) : shortMatrix a 1 *ᵥ w ∈ W := by
    apply mulVec_mem_fixedSubmodule K j (shortUnits a (Multiplicative.ofAdd (1 : K)))
      (fun T => shortOnePoint K a T) (fun T => ?_)
      (fun T h => hconj T _ (shortOnePoint_mem K a T) h) hw
    rw [pointMatrix_shortOnePoint]
    change shortMatrix a (1 : Γ(T.left, ⊤)) = (shortMatrix a (1 : K)).map (scalarMap T)
    rw [shortMatrix_map, _root_.map_one]
  have hhyper (w : l ⊕ l → K) : evenVector w ∈ W := by
    apply evenVector_mem_of_stable W hW _ _ _ hShort w
    · intro g w hw
      have hs := hEven (OrthogonalMatrix.leviHom K g)
        (fun T => OrthogonalMatrix.constantPoint_levi_mem T g) w hw
      rwa [evenBlock_levi] at hs
    · intro A hA w hw
      have hs := hEven ⟨SymplecticMatrix.upper A, OrthogonalMatrix.upper_mem hA⟩
        (fun T => OrthogonalMatrix.constantPoint_upper_mem T hA) w hw
      rwa [evenBlock_upper K hA] at hs
    · intro A hA w hw
      have hs := hEven ⟨SymplecticMatrix.lower A, OrthogonalMatrix.lower_mem hA⟩
        (fun T => OrthogonalMatrix.constantPoint_lower_mem T hA) w hw
      rwa [evenBlock_lower K hA] at hs
  have hfix (a : l ⊕ l) : Pi.single (Sum.inr a) (1 : K) ∈ W := by
    have hs := hhyper (Pi.single a 1)
    have he : evenVector (Pi.single a (1 : K)) = Pi.single (Sum.inr a) 1 := by
      ext (i | i) <;> simp [evenVector, Pi.single_apply]
    rwa [he] at hs
  have hj : j.hom.hom = 1 := hom_eq_one_of_even_fixed K j hfix
  have hm : Mono (identityComponentι 𝐆).hom.hom := by
    rw [IdentityComponent.identityComponentι_hom_hom]
    infer_instance
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    apply (cancel_mono (identityComponentι 𝐆).hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, MonObj.one_comp]
    change h ≫ j.hom.hom = 1
    rw [hj, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

variable (l)

set_option linter.defProp false in
/-- The actual identity component of the split odd norm-one group is
pseudo-reductive over every field, with at least two hyperbolic indices. -/
def identityPseudoReductive [Nontrivial l] : IsPseudoReductive (identityComponent (groupScheme l K)) where
  smooth := inferInstance
  isAffineHom := inferInstance
  connectedSpace := inferInstance
  hasTrivialUnipotentRadical := hasTrivialUnipotentRadical_identityComponent K

end Langlands.GroupScheme.OddOrthogonalMatrix
