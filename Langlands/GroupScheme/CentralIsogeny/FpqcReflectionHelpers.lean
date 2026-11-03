import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Proof helpers for fpqc reflection of central isogenies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
variable {G H : GroupScheme S}

/-- Flat surjective base change detects centrality on every actual test scheme. -/
theorem IsCentral.of_baseChange [Surjective b] [Flat b] {i : H ⟶ G}
    (hi : IsCentral ((GroupScheme.baseChange b).map i)) : IsCentral i := by
  intro T x
  apply mem_center.mpr
  intro T' a y
  change (a ≫ (x ≫ i.hom.hom)) * y = y * (a ≫ (x ≫ i.hom.hom))
  let V : Over S' := (Over.pullback b).obj T'
  let q : (Over.map b).obj V ⟶ T' :=
    Over.homMk (pullback.fst T'.hom b) pullback.condition
  have hq : Epi q.left := by
    change Epi (pullback.fst T'.hom b)
    exact Flat.epi_of_flat_of_surjective _
  let x' : V ⟶ ((GroupScheme.baseChange b).obj H).X :=
    (baseChangePointsEquiv b H V).symm (q ≫ a ≫ x)
  let y' : V ⟶ ((GroupScheme.baseChange b).obj G).X :=
    (baseChangePointsEquiv b G V).symm (q ≫ y)
  have hc := congrArg (baseChangePointsEquiv b G V)
    (commute_of_mem_center (hi V x') y').eq
  have hp : q ≫ ((a ≫ (x ≫ i.hom.hom)) * y) =
      q ≫ (y * (a ≫ (x ≫ i.hom.hom))) := by
    simpa only [map_mul, baseChangePointsEquiv_comp, x', y', MulEquiv.apply_symm_apply,
      MonObj.comp_mul, Category.assoc] using hc
  apply Over.OverMorphism.ext
  apply (cancel_epi q.left).mp
  exact congrArg (fun z => z.left) hp

/-- Kernel centrality reflects through the actual kernel base-change comparison. -/
theorem isCentral_kernelι_of_baseChange [Surjective b] [Flat b] (f : G ⟶ H)
    (hf : IsCentral (kernelι ((GroupScheme.baseChange b).map f))) :
    IsCentral (kernelι f) := by
  apply IsCentral.of_baseChange b
  have hc := hf.comp (kernelBaseChangeIso b f).hom
  simpa only [kernelBaseChangeIso_hom_ι] using hc

end Langlands.GroupScheme
