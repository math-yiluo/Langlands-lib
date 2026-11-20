import Langlands.LocalFactor.Ramification.Herbrand.TruncationGaloisComapProof
import Langlands.ClassFieldTheory.Local.IntermediateReciprocityTransport

namespace Langlands.Ramification.Kummer

open LocalClassField Weil.Local
open _root_.Langlands.Ramification.Padic

universe u

private theorem galoisQuotientIsoAlong_of_comap {p : ℕ} [Fact p.Prime]
    (K F : PadicField.{u} p)
    (ι : Field.absoluteGaloisGroup K.Carrier →ₜ* Field.absoluteGaloisGroup F.Carrier)
    (x : ℝ) (hx : -1 ≤ x)
    (hcomap : ∀ y : ℝ, -1 ≤ y → y ≤ x →
      (absoluteUpperRamificationGroup F y).comap ι.toMonoidHom =
        absoluteUpperRamificationGroup K y)
    (hsplit : ∀ g : Field.absoluteGaloisGroup F.Carrier,
      ∃ a : Field.absoluteGaloisGroup K.Carrier,
        ∃ n ∈ absoluteUpperRamificationGroup F x, ι a * n = g) :
    GaloisQuotientIsoAlong K F ι x := by
  let f := (QuotientGroup.mk' (absoluteUpperRamificationGroup F x)).comp ι.toMonoidHom
  have hker : absoluteUpperRamificationGroup K x = f.ker := by
    calc
      _ = (absoluteUpperRamificationGroup F x).comap ι.toMonoidHom :=
        (hcomap x hx le_rfl).symm
      _ = (QuotientGroup.mk' (absoluteUpperRamificationGroup F x)).ker.comap ι.toMonoidHom :=
        congrArg (Subgroup.comap ι.toMonoidHom) (QuotientGroup.ker_mk' _).symm
      _ = f.ker := MonoidHom.comap_ker _ _
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, n, hn, han⟩ := hsplit g
    exact ⟨a, (QuotientGroup.mk'_eq_mk' _).mpr ⟨n, hn, han⟩⟩
  let e := QuotientGroup.liftEquiv (absoluteUpperRamificationGroup K x) hsurj hker
  have hcont : Continuous e :=
    (QuotientGroup.isQuotientMap_mk (absoluteUpperRamificationGroup K x)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp ι.continuous)
  have : CharZero K.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) K.Carrier).injective
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  let : CompactSpace (Field.absoluteGaloisGroup K.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K.Carrier/K.Carrier))
  let : IsClosed (absoluteUpperRamificationGroup F x : Set (Field.absoluteGaloisGroup F.Carrier)) :=
    absoluteUpperRamificationGroup_isClosed F x
  let φ : (Field.absoluteGaloisGroup K.Carrier ⧸ absoluteUpperRamificationGroup K x) ≃ₜ*
      (Field.absoluteGaloisGroup F.Carrier ⧸ absoluteUpperRamificationGroup F x) :=
    { toMulEquiv := e
      continuous_toFun := hcont
      continuous_invFun := hcont.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }
  refine ⟨φ, fun a => rfl, ?_⟩
  intro y hy hyx
  rw [Set.image_image]
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨ι a, ?_, rfl⟩
    change a ∈ absoluteUpperRamificationGroup K y at ha
    rw [← hcomap y hy hyx, Subgroup.mem_comap] at ha
    exact ha
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, n, hn, han⟩ := hsplit g
    refine ⟨a, ?_, ?_⟩
    · change a ∈ absoluteUpperRamificationGroup K y
      rw [← hcomap y hy hyx, Subgroup.mem_comap]
      have hn' := absoluteUpperRamificationGroup_antitone F hyx hn
      have hm := (absoluteUpperRamificationGroup F y).mul_mem hg
        ((absoluteUpperRamificationGroup F y).inv_mem hn')
      rwa [← han, mul_inv_cancel_right] at hm
    · change QuotientGroup.mk' (absoluteUpperRamificationGroup F x) (ι a) =
        QuotientGroup.mk' (absoluteUpperRamificationGroup F x) g
      exact (QuotientGroup.mk'_eq_mk' _).mpr ⟨n, hn, han⟩

/-- Through the transitivity index, the intermediate Galois map induces filtered topological
isomorphisms of the absolute Galois quotients. -/
theorem truncationGaloisQuotient : TruncationGaloisQuotientStatement.{u} := by
  intro p _ F E μ htrans x hx hxμ
  refine galoisQuotientIsoAlong_of_comap (E.asPadicField (p := p)) F
    (intermediateGaloisMap F E) x hx
    (fun y hy hyx => truncationGaloisComap p F E μ htrans y hy (hyx.trans hxμ)) ?_
  intro g
  have hg : g ∈ E.field.fixingSubgroup ⊔ absoluteUpperRamificationGroup F μ := by
    rw [htrans]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, n, hn, hhn⟩ :=
    (Subgroup.mem_sup_of_normal_right (ht := absoluteUpperRamificationGroup_normal F μ)).mp hg
  rw [← intermediateGaloisMap_range F E] at hh
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hh
  exact ⟨a, n, absoluteUpperRamificationGroup_antitone F hxμ hn, ha.symm ▸ hhn⟩

end Langlands.Ramification.Kummer
