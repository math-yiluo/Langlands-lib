import Langlands.Representation.Geometric.OrbitSectionExtensionStatement
import Langlands.Representation.Geometric.CosetOrbitHomeomorph
import Langlands.Representation.Geometric.OrbitRestriction
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Representation.Induction.CompactQuotientCutoff

/-! Compact extension by local covariant sections and finite clopen gluing. -/

noncomputable section
open scoped Classical

namespace Langlands.Geometric

universe uG uV

private theorem locallyClosed_of_closed_in_open
    {X : Type*} [TopologicalSpace X] {U Z : Set X}
    (hU : IsOpen U) (hZU : Z ⊆ U)
    (hZ : IsClosed ((fun x : U => (x : X)) ⁻¹' Z)) : IsLocallyClosed Z := by
  obtain ⟨C, hC, hCZ⟩ := Topology.IsInducing.subtypeVal.isClosed_iff.mp hZ
  refine ⟨U, C, hU, hC, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨hZU hx, (Set.ext_iff.mp hCZ ⟨x, hZU hx⟩).mpr hx⟩
  · rintro ⟨hxU, hxC⟩
    exact (Set.ext_iff.mp hCZ ⟨x, hxU⟩).mp hxC

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Agreement at an orbit point persists on the intersection with an ambient
open neighborhood, using the actual orbit homeomorphism. -/
private theorem exists_open_orbit_agreement
    (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, e (Induction.quotientMap (orbitStabilizer P Q w) q) =
      cosetOrbitMap P Q w q)
    (σ : Representation ℂ P V) (f : Induction.SmoothFunctions P σ)
    (g : Induction.SmoothFunctions (orbitStabilizer P Q w)
      (σ.comp (stabilizerToInducing P Q w))) (q : Q)
    (hq : Induction.eval P σ f (w⁻¹ * (q : G)) = Induction.eval _ _ g q) :
    ∃ W : Set (Induction.LeftQuotient P), IsOpen W ∧
      Induction.quotientMap P (w⁻¹ * (q : G)) ∈ W ∧
      ∀ r : Q, Induction.quotientMap P (w⁻¹ * (r : G)) ∈ W →
        Induction.eval P σ f (w⁻¹ * (r : G)) = Induction.eval _ _ g r := by
  let d := smoothOrbitRestriction P Q w σ f - g
  let S := Induction.quotientSupport (orbitStabilizer P Q w) (Induction.eval _ _ d)
  let D : Set (cosetOrbit P Q w) := e.symm ⁻¹' Sᶜ
  have hD : IsOpen D :=
    (Induction.isClosed_quotientSupport _ _ d).isOpen_compl.preimage e.symm.continuous
  have hmem (r : Q) : cosetOrbitMap P Q w r ∈ D ↔
      Induction.eval P σ f (w⁻¹ * (r : G)) = Induction.eval _ _ g r := by
    change e.symm (cosetOrbitMap P Q w r) ∉ S ↔ _
    rw [← he r, e.symm_apply_apply]
    have hs := Set.ext_iff.mp
      (Induction.quotientMap_preimage_quotientSupport (orbitStabilizer P Q w)
        (σ.comp (stabilizerToInducing P Q w)) d) r
    change (Induction.quotientMap (orbitStabilizer P Q w) r ∈ S ↔
      Induction.eval _ _ d r ≠ 0) at hs
    rw [hs, not_not]
    change Induction.eval P σ f (w⁻¹ * (r : G)) - Induction.eval _ _ g r = 0 ↔ _
    exact sub_eq_zero
  obtain ⟨W, hW, hWD⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hD
  refine ⟨W, hW, ?_, ?_⟩
  · exact (Set.ext_iff.mp hWD (cosetOrbitMap P Q w q)).mpr ((hmem q).mpr hq)
  · intro r hr
    exact (hmem r).mp ((Set.ext_iff.mp hWD (cosetOrbitMap P Q w r)).mp hr)

/-- Finite gluing replaces the old section on the next clopen set. This avoids
choosing disjoint representatives while retaining an actual compact section. -/
private theorem finite_orbit_gluing
    (P Q : Subgroup G) (w : G) (σ : Representation ℂ P V)
    (g : Induction.SmoothFunctions (orbitStabilizer P Q w)
      (σ.comp (stabilizerToInducing P Q w)))
    (cutoff : ∀ (C : Set (Induction.LeftQuotient P)), IsCompact C → IsClopen C →
      Induction.CompactFunctions P σ → Induction.CompactFunctions P σ)
    (hcutoff : ∀ C hc ho f x, Induction.eval P σ (cutoff C hc ho f).val x =
      if Induction.quotientMap P x ∈ C then Induction.eval P σ f.val x else 0)
    {I : Type*} (C : I → Set (Induction.LeftQuotient P))
    (hCc : ∀ i, IsCompact (C i)) (hCo : ∀ i, IsClopen (C i))
    (U : Set (Induction.LeftQuotient P)) (hCU : ∀ i, C i ⊆ U)
    (patch : I → Induction.CompactFunctions P σ)
    (hpatch : ∀ i (q : Q), Induction.quotientMap P (w⁻¹ * (q : G)) ∈ C i →
      Induction.eval P σ (patch i).val (w⁻¹ * (q : G)) = Induction.eval _ _ g q)
    (t : Finset I) :
    ∃ f : Induction.CompactFunctions P σ,
      (∀ x : G, Induction.eval P σ f.val x ≠ 0 → Induction.quotientMap P x ∈ U) ∧
      ∀ q : Q, Induction.eval P σ f.val (w⁻¹ * (q : G)) =
        if ∃ i ∈ t, Induction.quotientMap P (w⁻¹ * (q : G)) ∈ C i
        then Induction.eval _ _ g q else 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_, ?_⟩
    · intro x hx
      exact (hx rfl).elim
    · intro q
      simp [Induction.eval]
  | @insert i t hit ih =>
    obtain ⟨f, hfU, hfg⟩ := ih
    let f' := cutoff (C i) (hCc i) (hCo i) (patch i) +
      (f - cutoff (C i) (hCc i) (hCo i) f)
    have heval (x : G) : Induction.eval P σ f'.val x =
        if Induction.quotientMap P x ∈ C i then Induction.eval P σ (patch i).val x
        else Induction.eval P σ f.val x := by
      change Induction.eval P σ (cutoff (C i) (hCc i) (hCo i) (patch i)).val x +
        (Induction.eval P σ f.val x -
          Induction.eval P σ (cutoff (C i) (hCc i) (hCo i) f).val x) = _
      rw [hcutoff, hcutoff]
      split_ifs <;> simp
    refine ⟨f', ?_, ?_⟩
    · intro x hx
      by_cases hxi : Induction.quotientMap P x ∈ C i
      · exact hCU i hxi
      · exact hfU x (by simpa only [heval, ite_eq_right hxi] using hx)
    · intro q
      rw [heval]
      by_cases hqi : Induction.quotientMap P (w⁻¹ * (q : G)) ∈ C i
      · rw [ite_eq_left hqi, hpatch i q hqi, ite_eq_left]
        exact ⟨i, Finset.mem_insert_self i t, hqi⟩
      · rw [ite_eq_right hqi, hfg q]
        have hequiv : (∃ j ∈ insert i t,
            Induction.quotientMap P (w⁻¹ * (q : G)) ∈ C j) ↔
            ∃ j ∈ t, Induction.quotientMap P (w⁻¹ * (q : G)) ∈ C j := by
          constructor
          · rintro ⟨j, hjt, hj⟩
            rcases Finset.mem_insert.mp hjt with rfl | hjt
            · exact (hqi hj).elim
            · exact ⟨j, hjt, hj⟩
          · rintro ⟨j, hjt, hj⟩
            exact ⟨j, Finset.mem_insert_of_mem hjt, hj⟩
        simp only [hequiv]

/-- The compactness and gluing argument, separated from the constructions of
local sections and quotient cutoffs. -/
private theorem extension_of_local_sections
    (P Q : Subgroup G) (w : G)
    (e : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w)
    (he : ∀ q : Q, e (Induction.quotientMap (orbitStabilizer P Q w) q) =
      cosetOrbitMap P Q w q)
    (σ : Representation ℂ P V)
    (g : Induction.CompactFunctions (orbitStabilizer P Q w)
      (σ.comp (stabilizerToInducing P Q w)))
    (hlocal : ∀ q : Q, ∃ f : Induction.CompactFunctions P σ,
      Induction.eval P σ f.val (w⁻¹ * (q : G)) = Induction.eval _ _ g.val q)
    (hnbhd : ∀ (y : Induction.LeftQuotient P) (W : Set (Induction.LeftQuotient P)),
      IsOpen W → y ∈ W → ∃ C, IsCompact C ∧ IsClopen C ∧ y ∈ C ∧ C ⊆ W)
    (cutoff : ∀ (C : Set (Induction.LeftQuotient P)), IsCompact C → IsClopen C →
      Induction.CompactFunctions P σ → Induction.CompactFunctions P σ)
    (hcutoff : ∀ C hc ho f x, Induction.eval P σ (cutoff C hc ho f).val x =
      if Induction.quotientMap P x ∈ C then Induction.eval P σ f.val x else 0)
    (U : Set (Induction.LeftQuotient P)) (hU : IsOpen U) (hZU : cosetOrbit P Q w ⊆ U) :
    ∃ f : Induction.CompactFunctions P σ,
      (∀ x : G, Induction.eval P σ f.val x ≠ 0 → Induction.quotientMap P x ∈ U) ∧
      ∀ q : Q, Induction.eval P σ f.val (w⁻¹ * (q : G)) = Induction.eval _ _ g.val q := by
  classical
  have hpatches (q : Q) : ∃ C : Set (Induction.LeftQuotient P),
      IsCompact C ∧ IsClopen C ∧ Induction.quotientMap P (w⁻¹ * (q : G)) ∈ C ∧
      C ⊆ U ∧ ∃ f : Induction.CompactFunctions P σ,
        ∀ r : Q, Induction.quotientMap P (w⁻¹ * (r : G)) ∈ C →
          Induction.eval P σ f.val (w⁻¹ * (r : G)) = Induction.eval _ _ g.val r := by
    obtain ⟨f, hf⟩ := hlocal q
    obtain ⟨W, hW, hqW, hagree⟩ := exists_open_orbit_agreement P Q w e he σ f.val g.val q hf
    obtain ⟨C, hCc, hCo, hqC, hCW⟩ := hnbhd
      (Induction.quotientMap P (w⁻¹ * (q : G))) (W ∩ U) (hW.inter hU)
      ⟨hqW, hZU ⟨q, rfl⟩⟩
    exact ⟨C, hCc, hCo, hqC, fun _ hx => (hCW hx).2, f,
      fun r hr => hagree r (hCW hr).1⟩
  choose C hCc hCo hCq hCU patch hpatch using hpatches
  let K := (fun z => (e z).val) ''
    Induction.quotientSupport (orbitStabilizer P Q w) (Induction.eval _ _ g.val)
  have hK : IsCompact K := g.property.image (continuous_subtype_val.comp e.continuous)
  have hcover : K ⊆ ⋃ q : Q, C q := by
    rintro _ ⟨z, hz, rfl⟩
    induction z using Quotient.inductionOn with
    | h q =>
      change (e (Induction.quotientMap (orbitStabilizer P Q w) q)).val ∈ ⋃ q, C q
      rw [he q]
      exact Set.mem_iUnion.mpr ⟨q, hCq q⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover C (fun q => (hCo q).isOpen) hcover
  obtain ⟨f, hfU, hfg⟩ := finite_orbit_gluing P Q w σ g.val cutoff hcutoff
    C hCc hCo U hCU patch hpatch t
  refine ⟨f, hfU, fun q => ?_⟩
  rw [hfg q]
  by_cases hq : Induction.eval _ _ g.val q = 0
  · simp only [hq, ite_self]
  · apply ite_eq_left
    have hqK : Induction.quotientMap P (w⁻¹ * (q : G)) ∈ K := by
      refine ⟨Induction.quotientMap (orbitStabilizer P Q w) q, ⟨q, hq, rfl⟩, ?_⟩
      exact congrArg Subtype.val (he q)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hqK)
    obtain ⟨hit, hCi⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit, hCi⟩

/-- Every compact orbit section extends to an actual compactly induced section
supported in the prescribed open set. -/
theorem closedOrbitSectionExtension : ClosedOrbitSectionExtension.{uG,uV} := by
  intro G _ _ _ _ _ _ P Q hP hQ w U hU hZU hZ A g
  let hw := locallyClosed_of_closed_in_open hU hZU hZ
  let e := cosetOrbitHomeomorph P Q w hP hQ hw
  refine extension_of_local_sections P Q w e (fun _ => rfl) A.obj.ρ g ?_
    (Induction.exists_compactClopen_quotientNeighborhood P hP)
    (Induction.compactQuotientCutoff P A.obj.ρ)
    (Induction.eval_compactQuotientCutoff P A.obj.ρ) U hU hZU
  intro q
  let x := w⁻¹ * (q : G)
  let v := Induction.eval _ _ g.val q
  exact ⟨Induction.compactLocalSection P A.obj.ρ A.property x v Set.univ
      isOpen_univ (Set.mem_univ _),
    Induction.compactLocalSection_apply P A.obj.ρ A.property x v Set.univ
      isOpen_univ (Set.mem_univ _)⟩

end Langlands.Geometric
