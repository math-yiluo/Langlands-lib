import Langlands.BushnellKutzko.CoprimeRepresentationExtensionStatement
import Langlands.BushnellKutzko.CoprimeExtensionTransfer

/-! # Extending an irreducible representation by a scalar correction -/

noncomputable section

open Representation

namespace Langlands.BushnellKutzko

universe uG uW

variable {G : Type uG} [Group G] {N : Subgroup G} [N.Normal]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "U" => (Module.End ℂ W)ˣ

private def scalarUnits : ℂˣ →* U := Units.map (algebraMap ℂ (Module.End ℂ W)).toMonoidHom

private theorem scalarUnits_commute (a : ℂˣ) (T : U) : Commute (scalarUnits a) T := by
  apply Units.ext
  exact Algebra.commutes (a : ℂ) (T : Module.End ℂ W)

private theorem scalarUnits_injective [Nontrivial W] : Function.Injective (scalarUnits (W := W)) := by
  intro a b h
  apply Units.ext
  exact smul_left_injective ℂ (one_ne_zero : (1 : Module.End ℂ W) ≠ 0)
    (congrArg Units.val h : (a : ℂ) • (1 : Module.End ℂ W) = (b : ℂ) • 1)

omit [N.Normal] in
private theorem exists_scalar_of_commutes [FiniteDimensional ℂ W]
    (η : Representation ℂ N W) [η.IsIrreducible] (T : U)
    (hT : ∀ n : N, Commute T (η.toHomUnits n)) : ∃ c : ℂˣ, scalarUnits c = T := by
  let _ : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) η.asModule
  let f : η.IntertwiningMap η := ⟨T.val, fun n => congrArg Units.val (hT n).eq⟩
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := η)).surjective f
  have hc' : c • (1 : Module.End ℂ W) = T.val := congrArg IntertwiningMap.toLinearMap hc
  have hc₀ : c ≠ 0 := by
    intro he
    rw [he, zero_smul] at hc'
    exact T.ne_zero hc'.symm
  exact ⟨Units.mk0 c hc₀, Units.ext hc'⟩

private def representationGraph (η : Representation ℂ N W) : N →* G × U :=
  N.subtype.prod η.toHomUnits

private theorem mem_graph_normalizer (η : Representation ℂ N W) (g : G) (T : U) :
    (g, T) ∈ Subgroup.normalizer ((representationGraph η).range : Set (G × U)) ↔
      ∀ n : N, T * η.toHomUnits n * T⁻¹ = η.toHomUnits (MulAut.conjNormal g n) := by
  constructor
  · intro h n
    have hn : representationGraph η n ∈ (representationGraph η).range := ⟨n, rfl⟩
    obtain ⟨m, hm⟩ := (Subgroup.mem_normalizer_iff.mp h _).mp hn
    have h₁ : m.val = g * n.val * g⁻¹ := congrArg Prod.fst hm
    have h₂ : η.toHomUnits m = T * η.toHomUnits n * T⁻¹ := congrArg Prod.snd hm
    rw [show m = MulAut.conjNormal g n from Subtype.ext h₁] at h₂
    exact h₂.symm
  · intro h
    have he : (MulAut.conj (g, T)).toMonoidHom.comp (representationGraph η) =
        (representationGraph η).comp (MulAut.conjNormal g).toMonoidHom := by
      apply MonoidHom.ext
      intro n
      exact Prod.ext rfl (h n)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_range]
    change ((MulAut.conj (g, T)).toMonoidHom.comp (representationGraph η)).range = _
    have htop : ((MulAut.conjNormal (H := N) g).toMonoidHom).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (MulAut.conjNormal (H := N) g).surjective
    rw [he, MonoidHom.range_comp, htop, Subgroup.map_top]

/-- The finite-index extension follows by correcting a conjugating operator with a scalar
character obtained from transfer and the determinant. -/
theorem coprimeRepresentationExtension : CoprimeRepresentationExtensionStatement.{uG, uW} := by
  classical
  intro G _ N P _ _ hNP W _ _ _ η hη hI hP a hdet hcop
  let _ : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) η.asModule
  let graph := representationGraph η
  let Γ := graph.range
  let K := Subgroup.normalizer (Γ : Set (G × (Module.End ℂ W)ˣ))
  let ΓK := Γ.subgroupOf K
  let _ : ΓK.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer Γ.le_normalizer).mpr le_rfl
  let proj := (MonoidHom.fst G (Module.End ℂ W)ˣ).comp K.subtype
  let op := (MonoidHom.snd G (Module.End ℂ W)ˣ).comp K.subtype
  let graphK : N →* K := graph.codRestrict K fun n => Γ.le_normalizer ⟨n, rfl⟩
  have hproj : Function.Surjective proj := by
    intro g
    obtain ⟨e⟩ := hI g
    let T := LinearMap.GeneralLinearGroup.ofLinearEquiv e.toLinearEquiv
    refine ⟨⟨(g, T), (mem_graph_normalizer η g T).mpr (fun n => ?_)⟩, rfl⟩
    apply mul_inv_eq_of_eq_mul
    apply Units.ext
    exact e.isIntertwining' n
  let scalars : ℂˣ →* K :=
    ((1 : ℂˣ →* G).prod (scalarUnits (W := W))).codRestrict K (fun c => by
      apply (mem_graph_normalizer η 1 (scalarUnits c)).mpr
      intro n
      rw [map_one MulAut.conjNormal]
      change scalarUnits c * η.toHomUnits n * (scalarUnits c)⁻¹ = η.toHomUnits n
      rw [(scalarUnits_commute c (η.toHomUnits n)).eq, mul_inv_cancel_right])
  have hscalar_inj : Function.Injective scalars := fun _ _ h =>
    scalarUnits_injective (congrArg op h)
  have hcentral (c : ℂˣ) (x : K) : Commute (scalars c) x := by
    apply Subtype.ext
    exact Prod.ext (by change 1 * x.val.1 = x.val.1 * 1; simp) (scalarUnits_commute c x.val.2).eq
  have hker (x : K) (hx : x ∈ proj.ker) : ∃ c : ℂˣ, scalars c = x := by
    have h1 : x.val.1 = 1 := hx
    have hcomm (n : N) : Commute x.val.2 (η.toHomUnits n) := by
      have he := (mem_graph_normalizer η x.val.1 x.val.2).mp x.property n
      rw [h1, map_one MulAut.conjNormal] at he
      change x.val.2 * η.toHomUnits n * x.val.2⁻¹ = η.toHomUnits n at he
      exact eq_mul_of_mul_inv_eq he
    obtain ⟨c, hc⟩ := exists_scalar_of_commutes η x.val.2 hcomm
    exact ⟨c, Subtype.ext (Prod.ext h1.symm hc)⟩
  obtain ⟨ηP, hηP⟩ := hP
  have hrest (n : N) : ηP.toHomUnits (Subgroup.inclusion hNP n) = η.toHomUnits n :=
    Units.ext (DFunLike.congr_fun hηP n)
  let liftP : P →* K :=
    (P.subtype.prod ηP.toHomUnits).codRestrict K (fun g => by
      apply (mem_graph_normalizer η g.val (ηP.toHomUnits g)).mpr
      intro n
      rw [← hrest n, ← hrest (MulAut.conjNormal g.val n),
        ← map_inv, ← map_mul, ← map_mul]
      exact congrArg ηP.toHomUnits (Subtype.ext rfl))
  have hlift (n : N) : liftP (Subgroup.inclusion hNP n) = graphK n :=
    Subtype.ext (Prod.ext rfl (hrest n))
  let H := P.comap proj
  let toP : H →* P :=
    (proj.comp H.subtype).codRestrict P fun x => x.property
  have hscalarsH (c : ℂˣ) : scalars c ∈ H := by
    change (1 : G) ∈ P
    exact P.one_mem
  have decomp (x : H) : ∃ c : ℂˣ, scalars c * liftP (toP x) = x.val := by
    have hm : x.val * (liftP (toP x))⁻¹ ∈ proj.ker := by
      change proj (x.val * (liftP (toP x))⁻¹) = 1
      rw [map_mul, map_inv]
      change x.val.val.1 * x.val.val.1⁻¹ = 1
      exact mul_inv_cancel _
    obtain ⟨c, hc⟩ := hker _ hm
    exact ⟨c, by rw [hc, inv_mul_cancel_right]⟩
  let c (x : H) := (decomp x).choose
  have hc (x : H) : scalars (c x) * liftP (toP x) = x.val := (decomp x).choose_spec
  have hc_eq (x : H) (z : ℂˣ) (hz : scalars z * liftP (toP x) = x.val) : c x = z :=
    hscalar_inj (mul_right_cancel ((hc x).trans hz.symm))
  let χ : H →* ℂˣ :=
    { toFun := c
      map_one' := hc_eq 1 1 (by simp)
      map_mul' := fun x y => hc_eq (x * y) (c x * c y) (by
        calc
          scalars (c x * c y) * liftP (toP (x * y)) =
              (scalars (c x) * liftP (toP x)) * (scalars (c y) * liftP (toP y)) := by
            simp only [map_mul, mul_assoc]
            rw [(hcentral (c y) (liftP (toP x))).left_comm]
          _ = (x * y).val := by rw [hc x, hc y]; rfl) }
  have hχ (z : ℂˣ) : χ ⟨scalars z, hscalarsH z⟩ = z := by
    apply hc_eq
    have he : toP ⟨scalars z, hscalarsH z⟩ = 1 := Subtype.ext rfl
    rw [he, map_one, mul_one]
  have hχΓ : ΓK.subgroupOf H ≤ χ.ker := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hnx : graphK n = x.val := Subtype.ext hn
    have hpn : toP x = Subgroup.inclusion hNP n :=
      Subtype.ext (congrArg proj hnx).symm
    change c x = 1
    apply hc_eq
    rw [hpn, hlift, map_one, one_mul, hnx]
  let δ : K →* ℂˣ :=
    ((Units.map (LinearMap.det : Module.End ℂ W →* ℂ)).comp op) ^ a
  have hδ (z : ℂˣ) : δ (scalars z) = z ^ (Module.finrank ℂ W * a) := by
    apply Units.ext
    change LinearMap.det ((z : ℂ) • (1 : Module.End ℂ W)) ^ a = _
    rw [LinearMap.det_smul, map_one, mul_one, pow_mul]
    rfl
  have hδΓ : ΓK ≤ δ.ker := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    have hnx : graphK n = x := Subtype.ext hn
    change δ x = 1
    rw [← hnx]
    apply Units.ext
    exact hdet n
  have hindex : H.index = P.index := P.index_comap_of_surjective hproj
  have hcIndex : H.index.Coprime (Module.finrank ℂ W * a) := hindex ▸ hcop
  obtain ⟨r, hr, hrΓ⟩ := exists_scalar_retraction_of_coprime scalars hcentral hscalarsH
    χ hχ hχΓ δ _ hδ hδΓ hcIndex
  let corrected : K →* (Module.End ℂ W)ˣ :=
    { toFun := fun x => (scalarUnits (r x))⁻¹ * op x
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, mul_inv_rev, mul_assoc]
        rw [(scalarUnits_commute (r y) (scalarUnits (r x))⁻¹).inv_left.left_comm,
          (scalarUnits_commute (r y) (op x)).inv_left.left_comm] }
  have hcorrected : proj.ker ≤ corrected.ker := by
    intro x hx
    obtain ⟨c, rfl⟩ := hker x hx
    change (scalarUnits (r (scalars c)))⁻¹ * scalarUnits c = 1
    rw [hr, inv_mul_cancel]
  let ρ := proj.liftOfSurjective hproj ⟨corrected, hcorrected⟩
  refine ⟨(Units.coeHom _).comp ρ, ?_⟩
  apply MonoidHom.ext
  intro n
  have hρ : ρ (proj (graphK n)) = corrected (graphK n) :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hrn : r (graphK n) = 1 := hrΓ (show graphK n ∈ ΓK from ⟨n, rfl⟩)
  change (ρ (proj (graphK n))).val = η n
  rw [hρ]
  change ((scalarUnits (r (graphK n)))⁻¹ * η.toHomUnits n).val = η n
  rw [hrn, map_one, inv_one, one_mul]
  rfl

end Langlands.BushnellKutzko
