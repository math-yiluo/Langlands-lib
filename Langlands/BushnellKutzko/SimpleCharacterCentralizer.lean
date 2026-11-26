import Langlands.BushnellKutzko.SimpleCharacters
import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.NormalizerProof
import Langlands.BushnellKutzko.RelativeLatticeChain

/-! # Relative units and determinant characters -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Restriction of scalars identifies the relative automorphisms with the centralizer units. -/
def relativeEndUnitEquiv (β : A) (hE : IsField (elementAlgebra β)) :
    letI := hE.toField
    (Module.End (elementAlgebra β) V)ˣ ≃* centralizerUnitGroup β := by
  letI := hE.toField
  let E := elementAlgebra β
  let ι := relativeEndUnits (F := F) (V := V) E
  let β₀ : E := ⟨β, Algebra.self_mem_adjoin_singleton F β⟩
  have hβ₀ : Algebra.adjoin F ({β₀} : Set E) = ⊤ := by
    apply Subalgebra.map_injective (f := E.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, Set.image_singleton]
    rfl
  have hβ : subfieldEmbedding F E V β₀ = β := by
    ext v
    rfl
  have hc (x : (Module.End E V)ˣ) : ι x ∈ centralizerUnitGroup β := by
    change Commute β ((x : Module.End E V).restrictScalars F)
    rw [← hβ]
    exact (restrictScalars_commute (x : Module.End E V) β₀).symm
  refine MulEquiv.ofBijective (ι.codRestrict (centralizerUnitGroup β) hc) ⟨?_, ?_⟩
  · intro x y h
    apply Units.ext
    apply LinearMap.restrictScalars_injective F
    exact congrArg (fun z : centralizerUnitGroup β => ((z : G) : A)) h
  · intro g
    have hcomm {x : G} (hx : x ∈ centralizerUnitGroup β) :
        Commute (x : A) (subfieldEmbedding F E V β₀) := by
      rw [hβ]
      exact (show Commute β (x : A) from hx).symm
    obtain ⟨a, ha⟩ := exists_restrictScalars_of_commute hβ₀ (hcomm g.property)
    obtain ⟨b, hb⟩ := exists_restrictScalars_of_commute hβ₀
      (hcomm ((centralizerUnitGroup β).inv_mem g.property))
    have hab : a * b = 1 := by
      apply LinearMap.restrictScalars_injective F
      change a.restrictScalars F * b.restrictScalars F = (1 : A)
      rw [ha, hb, Units.mul_inv]
    have hba : b * a = 1 := by
      apply LinearMap.restrictScalars_injective F
      change b.restrictScalars F * a.restrictScalars F = (1 : A)
      rw [hb, ha, Units.inv_mul]
    let u : (Module.End E V)ˣ := ⟨a, b, hab, hba⟩
    refine ⟨u, Subtype.ext (Units.ext ?_)⟩
    exact ha

@[simp]
theorem coe_relativeEndUnitEquiv (β : A) (hE : IsField (elementAlgebra β)) :
    letI := hE.toField
    ∀ x : (Module.End (elementAlgebra β) V)ˣ,
      (relativeEndUnitEquiv β hE x : G) = relativeEndUnits (elementAlgebra β) x := by
  intro x
  rfl

/-- A determinant character is invariant under centralizer conjugation on the overlap
of its relative domain and the conjugate of that domain. -/
theorem factorsThroughCentralizerDet.conj_eq {β : A} {H : Subgroup G} {χ : H →* ℂˣ}
    (hχ : factorsThroughCentralizerDet β χ) {g : G} (hg : g ∈ centralizerUnitGroup β)
    (x : H) (hx : (x : G) ∈ centralizerUnitGroup β) (hconj : g * (x : G) * g⁻¹ ∈ H) :
    χ ⟨_, hconj⟩ = χ x := by
  obtain ⟨hE, hχ⟩ := hχ
  let := hE.toField
  let E := elementAlgebra β
  let ι := relativeEndUnits (F := F) (V := V) E
  let e := relativeEndUnitEquiv β hE
  let a := e.symm ⟨g, hg⟩
  let b := e.symm ⟨x, hx⟩
  have ha : ι a = g := congrArg (fun y : centralizerUnitGroup β => (y : G)) (e.apply_symm_apply _)
  have hb : ι b = x := congrArg (fun y : centralizerUnitGroup β => (y : G)) (e.apply_symm_apply _)
  have hab : ι (a * b * a⁻¹) = g * (x : G) * g⁻¹ := by simp only [map_mul, map_inv, ha, hb]
  let U := H.comap ι
  let d : (Module.End E V)ˣ →* Eˣ := Units.map (LinearMap.det : Module.End E V →* E)
  let f := d.comp U.subtype
  let y : U := ⟨b, show ι b ∈ H from hb.symm ▸ x.property⟩
  let z : U := ⟨a * b * a⁻¹, show ι (a * b * a⁻¹) ∈ H from hab.symm ▸ hconj⟩
  obtain ⟨η, hη⟩ := hχ
  have heq : f.rangeRestrict z = f.rangeRestrict y := by
    apply Subtype.ext
    change d (a * b * a⁻¹) = d b
    rw [map_mul, map_mul, map_inv, mul_comm (d a) (d b), mul_assoc, mul_inv_cancel, mul_one]
  calc
    χ ⟨_, hconj⟩ = χ ⟨ι z, z.property⟩ := congrArg χ (Subtype.ext hab.symm)
    _ = η (f.rangeRestrict z) := hη z
    _ = η (f.rangeRestrict y) := congrArg η heq
    _ = χ ⟨ι y, y.property⟩ := (hη y).symm
    _ = χ x := congrArg χ (Subtype.ext hb)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- A centralizer unit normalizing a relative congruence subgroup preserves the relative
lattice chain. -/
theorem mem_relativeOrderNormalizer_of_normalizes_relativeUnits
    (S : Stratum 𝒪[F] F V) (hS : S.IsPure) (m : ℕ)
    {g : G} (hg : g ∈ centralizerUnitGroup S.b)
    (hgN : g ∈ Subgroup.normalizer (relativeUnitFiltration S.chain S.b m : Set G)) :
    g ∈ relativeOrderNormalizer S.chain S.b := by
  obtain ⟨hE, hnormal⟩ := hS.1
  let E := elementAlgebra S.b
  let : Field E := hE.toField
  let := S.chain.finiteDimensional
  let : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra S.b))
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let C := S.chain.relativeLatticeChain hnormal (isIntegral_iff_mem_spectralInteger F E)
  let ι := relativeEndUnits (F := F) (V := V) E
  let e := relativeEndUnitEquiv S.b hE
  let u := e.symm ⟨g, hg⟩
  have hu : ι u = g := congrArg (fun y : centralizerUnitGroup S.b => (y : G)) (e.apply_symm_apply _)
  have hU (t : (Module.End E V)ˣ) :
      t ∈ C.unitFiltration m ↔ ι t ∈ relativeUnitFiltration S.chain S.b m :=
    ⟨fun ht => ⟨(e t).property, ht⟩, fun ht => ht.2⟩
  have huN : u ∈ Subgroup.normalizer (C.unitFiltration m : Set (Module.End E V)ˣ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    rw [hU t, hU (u * t * u⁻¹), map_mul, map_mul, map_inv, hu]
    exact (Subgroup.mem_normalizer_iff.mp hgN) (ι t)
  rw [(normalizer E V C).2.2.1 m] at huN
  refine ⟨hg, S.chain.mem_stabilizer.mpr ?_⟩
  intro i
  obtain ⟨j, hj⟩ := C.mem_stabilizer.mp huN i
  refine ⟨j, ?_⟩
  rw [← hu]
  ext v
  exact SetLike.ext_iff.mp hj v

end Langlands.BushnellKutzko
