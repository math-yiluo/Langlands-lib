import Langlands.Geometry.Building.RootValueTorusFieldRestriction
import Langlands.Geometry.Building.KPBuilding

/-! # Descended root filtrations lie in the sharp fixer over the extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}

private instance filtrationSharpFixerAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

omit [IsAffineHom G.X.hom] in
/-- A factorization `S → T → G` of a torus embedding remains a factorization after scalar
extension to `K`. -/
theorem baseChange_groupHom_comp_of_factorization {iS : S.toGrp ⟶ G} {iT : T.toGrp ⟶ G}
    (f : S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = iS) :
    CommGroupScheme.groupHom ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f) ≫
        (GroupScheme.baseChange (algebraBaseMap k K)).map iT =
      (GroupScheme.baseChange (algebraBaseMap k K)).map iS := by
  rw [← hf, Functor.map_comp]
  rfl

variable [Smooth G.X.hom]

/-- **Descended root filtrations lie in the sharp fixer over `K`** (KP §9.2–9.3: the
filtration subgroups of the descended valuation are the `k`-points of the filtration
subgroups over `K`). Let `S → T → G` factor a torus embedding `iS` with `S` split over `k`,
let `T_K` be split with embedding `iT_K` in `G_K` having opposite factor pairs, let `D` be
any apartment class for `(G_K, T_K)` and `x` a point of its apartment, and let `w` be a point
of any apartment class `DS` for `(G, S)` whose valuation is the torus-then-field restriction
of `x`. Then for every root `a` of `(G, S)`, the depth-zero filtration group `U_{a,w,0}` lies
in the preimage of the sharp fixer `G(K)^♯_x` under `G(k) → G(K)`. -/
theorem filtration_le_comap_sharpFixer_of_torusFieldRestriction
    {iS : S.toGrp ⟶ G} [Mono iS.hom.hom.left] {iT : T.toGrp ⟶ G}
    (f : S ⟶ T) (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map iT).hom.hom.left]
    (hS : IsSplitTorus S.toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs
      (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iT))
    {ω : Kˣ → ℝ}
    (D : KPApartmentData (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map iT) ω)
    (x : D.Apartment) {ω' : kˣ → ℝ} (DS : KPApartmentData iS ω') (w : DS.Apartment)
    (hw : w.val = torusFieldRestrictedRootFunctionFamily (k := k) (K := K) hS hT hE
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f))
    (a : relativeRoots iS) :
    DS.filtration w a 0 ≤ (D.sharpFixer {x}).comap (rationalExtend k K G) := by
  have hfactor := baseChange_groupHom_comp_of_factorization (k := k) (K := K) f hf
  intro g hg
  have hg' : g ∈ rootFiltration iS w.val a 0 := hg
  rw [hw, rootFiltration_torusFieldRestrictedRootFunctionFamily iS hS hT hE
    (D.isRootDatumValuation_of_mem x.mem) _ hfactor a a.2 0] at hg'
  change rationalExtend k K G g ∈ torusRestrictedRootDepthSubgroup
    (D.isRootDatumValuation_of_mem x.mem)
    ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
    (characterLattice.baseChange (algebraBaseMap k K) S a) 0 at hg'
  refine (show torusRestrictedRootDepthSubgroup (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
      (characterLattice.baseChange (algebraBaseMap k K) S a) 0 ≤ D.sharpFixer {x} from ?_) hg'
  refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
    iSup_le fun _ => iSup_le fun _ => ?_
  rw [mul_zero]
  have h := D.rootFixer_le_sharpFixer ⟨χ, hχ⟩ {x}
  rw [D.rootFixer_singleton] at h
  exact h

end Langlands.Geometry.Building
