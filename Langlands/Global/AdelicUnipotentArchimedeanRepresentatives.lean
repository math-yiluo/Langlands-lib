import Langlands.Global.AdelicUnipotentStrongApproximation
import Langlands.Global.UnipotentRationalQuotientCompactProof
import Langlands.Global.AdelicOpenIwasawaCompact

/-! # Compact archimedean representatives at a fixed finite level -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Filter IsDedekindDomain NumberField Set Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G U : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine U.X.left]
  (j : U ⟶ G)

local notation "A" => AdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "Uf" => FiniteAdelicGroupPoints F U
local notation "U∞" => InfiniteAdelicGroupPoints F U
local notation "m" => map F U G j

private theorem map_ofFinite_eq (z : Uf) :
    m (ofFinite F U z) =
      ofFinite F G (U.affinePointsTarget j (CommAlgCat.of F (FiniteAdeles F)) z) := by
  have hi (a : AdelicGroupPoints F U) : infinite F G (m a) =
      U.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) (infinite F U a) :=
    DFunLike.congr_fun (U.affinePointsTarget_naturality j
      (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeles F)))) a
  apply (split F G).injective
  simp only [split_apply, hi, finite_map, infinite_ofFinite, finite_ofFinite, map_one]

/-- On a compact finite slice and at an open right level, every unipotent left translate can
be replaced by one from a fixed compact archimedean set, modulo rational left translation. -/
def AdelicUnipotentArchimedeanRepresentativesStatement [Smooth U.X.hom] : Prop :=
  ConnectedSpace U.X.left → IsUnipotent U →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
    ∃ D : Set U∞, IsCompact D ∧
      ∀ a : AdelicGroupPoints F U, ∃ v ∈ D, ∃ q : RationalGroupPoints F U,
        ∀ x : A, finite F G x ∈ Yf → ∃ l : L,
          m (rational F U q) * (m a * x) = m (ofInfinite F U v) * x * ofFinite F G l.val

theorem adelicUnipotentArchimedeanRepresentatives [Smooth U.X.hom] :
    AdelicUnipotentArchimedeanRepresentativesStatement j := by
  classical
  intro hconn hU Yf hY L hL
  let mf : Uf →* Gf := U.affinePointsTarget j (CommAlgCat.of F (FiniteAdeles F))
  have hmf : Continuous mf := U.continuous_affinePointsTarget _ j
  let b (p : Uf × Gf) := p.2⁻¹ * mf p.1 * p.2
  have hb : Continuous b := (continuous_snd.inv.mul (hmf.comp continuous_fst)).mul continuous_snd
  have hnear : ∀ᶠ v in 𝓝 (1 : Uf), ∀ y ∈ Yf, y⁻¹ * mf v * y ∈ L := by
    apply hY.eventually_forall_of_forall_eventually
    intro y _
    exact (hL.preimage hb).mem_nhds (show b (1, y) ∈ L by simp [b])
  obtain ⟨V, hV, hVo, hV1⟩ := mem_nhds_iff.mp hnear
  have hd := adelicUnipotentStrongApproximation F U hconn hU
  obtain ⟨C, hC, hcov⟩ := exists_isCompact_rational_mul_mem_of_split
    perfectFieldUnipotentSplit splitUnipotentAffineTorsorStatement F U inferInstance hconn hU
  let O (r : RationalGroupPoints F U) : Set (AdelicGroupPoints F U) :=
    {a | finite F U (rational F U r * a) ∈ V}
  have hOo (r : RationalGroupPoints F U) : IsOpen (O r) :=
    hVo.preimage ((finite F U).continuous.comp (continuous_const.mul continuous_id))
  have hOc : C ⊆ ⋃ r, O r := by
    intro a _
    have hOpen : IsOpen ((fun v : Uf => v * finite F U a) ⁻¹' V) :=
      hVo.preimage (continuous_id.mul continuous_const)
    have hne : ((fun v : Uf => v * finite F U a) ⁻¹' V).Nonempty :=
      ⟨(finite F U a)⁻¹, by simpa only [mem_preimage, inv_mul_cancel] using hV1⟩
    obtain ⟨r, hr⟩ := hd.exists_mem_open hOpen hne
    exact mem_iUnion.mpr ⟨r, by simpa only [O, mem_ofPred_eq, mem_preimage, map_mul] using hr⟩
  obtain ⟨R, hR⟩ := hC.elim_finite_subcover O hOo hOc
  let D : Set U∞ := ⋃ r ∈ R, (fun a => infinite F U (rational F U r * a)) '' C
  have hD : IsCompact D := R.isCompact_biUnion fun r _ =>
    hC.image ((infinite F U).continuous.comp (continuous_const.mul continuous_id))
  refine ⟨D, hD, fun a => ?_⟩
  obtain ⟨_, ⟨r₀, rfl⟩, hr₀⟩ := hcov a
  obtain ⟨r, hrR, hr⟩ := mem_iUnion₂.mp (hR hr₀)
  let s := rational F U r * (rational F U r₀ * a)
  let v := infinite F U s
  let w := finite F U s
  have hv : v ∈ D := mem_iUnion₂.mpr ⟨r, hrR, _, hr₀, rfl⟩
  have hw : w ∈ V := hr
  refine ⟨v, hv, r * r₀, fun x hx => ?_⟩
  let y := finite F G x
  let l : L := ⟨y⁻¹ * mf w * y, hV hw y hx⟩
  have hsplit : s = ofInfinite F U v * ofFinite F U w := by
    rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul]
    exact (pair_projections F U s).symm
  have he : ofFinite F G (mf w) * x = x * ofFinite F G l.val := by
    change ofFinite F G (mf w) * x = x * ofFinite F G ((finite F G x)⁻¹ * mf w * finite F G x)
    rw [← finite_conjugation]
    group
  refine ⟨l, ?_⟩
  calc
    _ = m s * x := by simp [s, map_mul, mul_assoc]
    _ = m (ofInfinite F U v) * (ofFinite F G (mf w) * x) := by
      rw [hsplit, map_mul, map_ofFinite_eq, mul_assoc]
    _ = _ := by rw [he, ← mul_assoc]

end Langlands.Global.AdelicGroupPoints
