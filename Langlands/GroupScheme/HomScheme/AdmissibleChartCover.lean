import Langlands.GroupScheme.HomScheme.AdmissibleCharts
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Field coverage gives a Zariski cover of the admissible presheaf -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli.OpenCharts

variable {S : Scheme.{u}} {G : GroupScheme S}
variable {ι : Type u} {U : ι → Over S} {K : ∀ k, GroupScheme (U k).left}
variable (j : ∀ k, K k ⟶ (baseChange (U k).hom).obj G)
variable (hj : ∀ k, IsOpenChart (j k))

/-- The actual open locus where a total section is a value of a fixed chart. -/
def chartLocus (k : ι) {T : Scheme.{u}}
    (ξ : (totalAdmissiblePresheaf G).obj (op T)) : T.Opens :=
  (exists_open_pullback (j k) (hj k) ξ).choose

/-- The locus is tested by lifting after every scheme morphism. -/
theorem chartLocus_spec (k : ι) {T : Scheme.{u}}
    (ξ : (totalAdmissiblePresheaf G).obj (op T))
    (T' : Scheme.{u}) (b : T' ⟶ T) :
    (∃ a : T' ⟶ (U k).left,
      (chartMap (j k) (hj k)).app (op T') a =
        (totalAdmissiblePresheaf G).map b.op ξ) ↔
      Set.range b.base ⊆ chartLocus j hj k ξ :=
  (exists_open_pullback (j k) (hj k) ξ).choose_spec T' b

/-- Coverage of all field-valued subgroups covers every point of every
parameter scheme by these actual open loci. -/
theorem chartLocus_covers (hc : CoversFieldPoints j) {T : Scheme.{u}}
    (ξ : (totalAdmissiblePresheaf G).obj (op T)) (x : T) :
    ∃ k, x ∈ chartLocus j hj k ξ := by
  let b := T.fromSpecResidueField x
  let ζ := (totalAdmissiblePresheaf G).map b.op ξ
  let F := actualSubgroup ζ
  let r := admissibleRepresentative F
  obtain ⟨k, a, ha⟩ := hc (T.residueField x) ζ.1 r.group r.hom r.closed r.torus
  have he : (chartMap (j k) (hj k)).app (op (Spec (T.residueField x))) a.left = ζ :=
    (chartMap_app_eq_iff (j k) (hj k) a ζ rfl).mpr (ha.trans r.represents.2)
  have hmem := (chartLocus_spec j hj k ξ _ b).mp ⟨a.left, he⟩
  refine ⟨k, hmem ?_⟩
  change x ∈ Set.range (T.fromSpecResidueField x)
  rw [Scheme.range_fromSpecResidueField]
  exact Set.mem_singleton x

/-- The coproduct of the actual chart maps is locally surjective in the
big Zariski topology. -/
theorem isLocallySurjective (hc : CoversFieldPoints j) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun k => chartMap (j k) (hj k))) := by
  constructor
  intro T ξ
  let V : ι → T.Opens := fun k => chartLocus j hj k ξ
  let 𝒲 : T.OpenCover := Scheme.Cover.mkOfCovers ι (fun k => (V k : Scheme.{u}))
    (fun k => (V k).ι) (fun x => by
      obtain ⟨k, hk⟩ := chartLocus_covers j hj hc ξ x
      exact ⟨k, ⟨x, hk⟩, rfl⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒲.mem_grothendieckTopology
  intro Y g hg
  obtain ⟨k, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  let a' : Y ⟶ (V k : Scheme.{u}) := a
  obtain ⟨φ, hφ⟩ := (chartLocus_spec j hj k ξ (V k) (V k).ι).mpr
    (by rw [Scheme.Opens.range_ι])
  refine ⟨(Sigma.ι (fun k => yoneda.obj (U k).left) k).app (op Y) (a' ≫ φ), ?_⟩
  show ((Sigma.ι (fun k => yoneda.obj (U k).left) k) ≫
      Sigma.desc (fun k => chartMap (j k) (hj k))).app (op Y) (a' ≫ φ) =
    (totalAdmissiblePresheaf G).map (a' ≫ (V k).ι).op ξ
  erw [Sigma.ι_comp_desc, chartMap_app_comp, hφ, ← Functor.map_comp_apply, ← op_comp]

end Langlands.GroupScheme.TorusSubgroupModuli.OpenCharts
