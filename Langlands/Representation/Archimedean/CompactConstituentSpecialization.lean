import Langlands.Representation.Archimedean.ConstituentSpecialization
import Langlands.Representation.KFiniteDual
import Mathlib.RepresentationTheory.Intertwining

/-!
# Compact types in specialization of simple constituents

A finite sum of compact isotypic projections detects a fixed vector in an
admissible representation. These projections respect stable subspaces,
compact intertwiners, and passage to a constituent. This supplies the
finite-rank operator for affine specialization of the other generators.
-/

noncomputable section

open scoped MonoidAlgebra

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ConstituentCompression

variable {ι M N J : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup J]
  [Module ℂ M] [Module ℂ N] [Module ℂ J]

/-- A constituent for a family of operators is the target of an equivariant
surjection from a subspace stable under those operators. -/
def IsOperatorConstituent (L : ι → Module.End ℂ M) (H : ι → Module.End ℂ J) : Prop :=
  ∃ (W : Submodule ℂ M) (hW : ∀ i x, x ∈ W → L i x ∈ W) (f : W →ₗ[ℂ] J),
    Function.Surjective f ∧ ∀ i (x : W), f ⟨L i x, hW i x x.2⟩ = H i (f x)

private theorem isConstituent_lift {L : ι → Module.End ℂ M} {H : ι → Module.End ℂ J}
    (h : IsOperatorConstituent L H) :
    IsConstituent (FreeAlgebra.lift ℂ L) (FreeAlgebra.lift ℂ H) := by
  obtain ⟨W, hW, f, hf, heq⟩ := h
  let R (i : ι) : Module.End ℂ W :=
    ((L i).comp W.subtype).codRestrict W (fun x => hW i x x.2)
  have hincl (a : FreeAlgebra ℂ ι) (x : W) :
      (FreeAlgebra.lift ℂ R a x : M) = FreeAlgebra.lift ℂ L a x :=
    intertwines_lift W.subtype R L (fun _ _ => rfl) a x
  have hstable : IsStable (FreeAlgebra.lift ℂ L) W := by
    intro a x hx
    rw [← hincl a ⟨x, hx⟩]
    exact (FreeAlgebra.lift ℂ R a ⟨x, hx⟩).2
  refine ⟨W, hstable, f, hf, fun a x => ?_⟩
  have hx : (⟨FreeAlgebra.lift ℂ L a x, hstable a x x.2⟩ : W) =
      FreeAlgebra.lift ℂ R a x := Subtype.ext (hincl a x).symm
  rw [hx]
  exact intertwines_lift f R H heq a x

private theorem isOperatorConstituent_of_lift {L : ι → Module.End ℂ M}
    {H : ι → Module.End ℂ J} (h : IsConstituent (FreeAlgebra.lift ℂ L) (FreeAlgebra.lift ℂ H)) :
    IsOperatorConstituent L H := by
  obtain ⟨W, hW, f, hf, heq⟩ := h
  have hWL (i : ι) (x : M) (hx : x ∈ W) : L i x ∈ W := by
    simpa only [FreeAlgebra.lift_ι_apply] using hW (FreeAlgebra.ι ℂ i) x hx
  refine ⟨W, hWL, f, hf, fun i x => ?_⟩
  have hx : (⟨FreeAlgebra.lift ℂ L (FreeAlgebra.ι ℂ i) x, hW _ _ x.2⟩ : W) =
      ⟨L i x, hWL i x x.2⟩ := by
    apply Subtype.ext
    change FreeAlgebra.lift ℂ L (FreeAlgebra.ι ℂ i) x = L i x
    rw [FreeAlgebra.lift_ι_apply]
  have h := heq (FreeAlgebra.ι ℂ i) x
  rwa [hx, FreeAlgebra.lift_ι_apply] at h

private theorem isSimple_lift (L : ι → Module.End ℂ J)
    (hirr : ∀ U : Submodule ℂ J, (∀ i x, x ∈ U → L i x ∈ U) → U = ⊥ ∨ U = ⊤) :
    IsSimple (FreeAlgebra.lift ℂ L) := by
  intro j hj y
  let σ := FreeAlgebra.lift ℂ L
  let F : FreeAlgebra ℂ ι →ₗ[ℂ] J := (LinearMap.applyₗ j).comp σ.toLinearMap
  have hstable (i : ι) (x : J) (hx : x ∈ LinearMap.range F) : L i x ∈ LinearMap.range F := by
    obtain ⟨a, rfl⟩ := hx
    refine ⟨FreeAlgebra.ι ℂ i * a, ?_⟩
    change σ (FreeAlgebra.ι ℂ i * a) j = L i (σ a j)
    rw [map_mul, Module.End.mul_apply, FreeAlgebra.lift_ι_apply]
  rcases hirr _ hstable with h | h
  · have hm : j ∈ LinearMap.range F := ⟨1, by
      change σ 1 j = j
      rw [map_one, Module.End.one_apply]⟩
    rw [h, Submodule.mem_bot] at hm
    exact (hj hm).elim
  · exact LinearMap.range_eq_top.mp h y

variable {K : Type*} [Group K]

/-- The sum of the projections onto a finite set of compact isotypic components. -/
def compactBlockProjection (ρ : Representation ℂ K M) [IsSemisimpleModule ℂ[K] ρ.asModule]
    (s : Finset (KFiniteDual.Block ρ)) : Module.End ℂ M :=
  ∑ c ∈ s, KFiniteDual.proj c

private theorem exists_compactDetector [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] (ρ : Representation ℂ K M)
    (hfin : ∀ v : M, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : M) (ℓ : M →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : IsAdmissibleGKModule ρ) (x : M) :
    ∃ p : Module.End ℂ M, FiniteDimensional ℂ (LinearMap.range p) ∧ p x = x ∧
      (∀ (U : Subrepresentation ρ) (y : M), y ∈ U → p y ∈ U) ∧
      (∀ (E : Representation.IntertwiningMap ρ ρ) (y : M), p (E y) = E (p y)) := by
  classical
  let _ : IsSemisimpleModule ℂ[K] ρ.asModule := KFiniteDual.isSemisimpleModule hfin hcont
  obtain ⟨s, _, hs⟩ := KFiniteDual.exists_finset_proj (ρ := ρ) x
  let T (c : s) : Submodule ℂ M := (KFiniteDual.blockSub c.1).toSubmodule
  let _ (c : s) : FiniteDimensional ℂ (T c) :=
    KFiniteDual.finiteDimensional_block hfin hcont hadm c.1
  let p := compactBlockProjection ρ s
  have hpRange : LinearMap.range p ≤ ⨆ c : s, T c := by
    rintro _ ⟨y, rfl⟩
    simp only [p, compactBlockProjection, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun c hc =>
      le_iSup T ⟨c, hc⟩ (KFiniteDual.proj_mem c y)
  refine ⟨p, Submodule.finiteDimensional_of_le hpRange, ?_, ?_, ?_⟩
  · simpa only [p, compactBlockProjection, LinearMap.sum_apply] using hs
  · intro U y hy
    simp only [p, compactBlockProjection, LinearMap.sum_apply]
    exact Submodule.sum_mem U.toSubmodule fun c _ => KFiniteDual.proj_mem_of_mem c U hy
  · intro E y
    simp only [p, compactBlockProjection, LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun c _ =>
      KFiniteDual.blockProj_comm c (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ E) y

private theorem affineAction_zero (p : Module.End ℂ M) (L D : ι → Module.End ℂ M) :
    affineAction p L D 0 = FreeAlgebra.lift ℂ (Option.elim · p L) := by
  apply FreeAlgebra.hom_ext
  funext i
  cases i <;> simp

/-- An irreducible constituent for compact and infinitesimal generators persists
at zero in a second affine family when the families are isomorphic at
infinitely many parameters. The first compact action is locally finite with
continuous coefficients and admissible. -/
theorem isOperatorConstituent_of_compact_affine_isomorphisms
    [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [Nontrivial J]
    (ρ : Representation ℂ K M) (ρ' : Representation ℂ K N) (ρJ : Representation ℂ K J)
    (hfin : ∀ v : M, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : M) (ℓ : M →ₗ[ℂ] ℂ), Continuous fun k => ℓ (ρ k v))
    (hadm : IsAdmissibleGKModule ρ)
    (L D : ι → Module.End ℂ M) (L' D' : ι → Module.End ℂ N) (LJ : ι → Module.End ℂ J)
    {S : Set ℂ} (hS : S.Infinite)
    (hiso : ∀ z ∈ S, ∃ e : M ≃ₗ[ℂ] N,
      (∀ k x, e (ρ k x) = ρ' k (e x)) ∧
      (∀ i x, e ((L i + z • D i) x) = (L' i + z • D' i) (e x)))
    (hirr : ∀ U : Submodule ℂ J, (∀ k x, x ∈ U → ρJ k x ∈ U) →
      (∀ i x, x ∈ U → LJ i x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hJ : IsOperatorConstituent (Sum.elim (fun k => ρ k) L) (Sum.elim (fun k => ρJ k) LJ)) :
    IsOperatorConstituent (Sum.elim (fun k => ρ' k) L') (Sum.elim (fun k => ρJ k) LJ) := by
  classical
  obtain ⟨W, hW, f, hf, heq⟩ := hJ
  obtain ⟨j, hj⟩ := exists_ne (0 : J)
  obtain ⟨x, hx⟩ := hf j
  obtain ⟨p, hpFin, hpFix, hpMem, hpComm⟩ := exists_compactDetector ρ hfin hcont hadm (x : M)
  obtain ⟨z, hz⟩ := hS.nonempty
  obtain ⟨e₀, he₀, _⟩ := hiso z hz
  let q := e₀.toLinearMap.comp (p.comp e₀.symm.toLinearMap)
  have hqRange : LinearMap.range q ≤
      LinearMap.range (e₀.toLinearMap.comp (LinearMap.range p).subtype) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨p.rangeRestrict (e₀.symm y), rfl⟩
  have hqFin : FiniteDimensional ℂ (LinearMap.range q) :=
    Submodule.finiteDimensional_of_le hqRange
  have hpq (e : M ≃ₗ[ℂ] N) (he : ∀ k y, e (ρ k y) = ρ' k (e y)) (y : M) :
      e (p y) = q (e y) := by
    let c := e₀.symm.toLinearMap.comp e.toLinearMap
    have hc (k : K) (y : M) : c (ρ k y) = ρ k (c y) := by
      apply e₀.injective
      change e₀ (e₀.symm (e (ρ k y))) = e₀ (ρ k (e₀.symm (e y)))
      rw [he₀, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, he]
    have h := hpComm (c.intertwiningMap_of_isIntertwiningMap ρ ρ hc) y
    change p (c y) = c (p y) at h
    calc e (p y) = e₀ (c (p y)) := (e₀.apply_symm_apply _).symm
      _ = e₀ (p (c y)) := congrArg e₀ h.symm
      _ = q (e y) := rfl
  let WK : Subrepresentation ρ := ⟨W, fun k _ hw => hW (.inl k) _ hw⟩
  let P : Module.End ℂ W := (p.comp W.subtype).codRestrict W (fun w => hpMem WK w w.2)
  let U : Subrepresentation ρ :=
    { toSubmodule := (LinearMap.ker f).map W.subtype
      apply_mem_toSubmodule := by
        rintro k _ ⟨w, hw, rfl⟩
        refine ⟨⟨ρ k w, hW (.inl k) _ w.2⟩, ?_, rfl⟩
        change f w = 0 at hw
        change f ⟨ρ k w, hW (.inl k) _ w.2⟩ = 0
        exact (heq (.inl k) w).trans ((congrArg (ρJ k) hw).trans (map_zero _)) }
  have hpKer : LinearMap.ker f ≤ LinearMap.ker (f.comp P) := by
    intro w hw
    have hm : p w ∈ U := hpMem U w ⟨w, hw, rfl⟩
    obtain ⟨w', hw', he⟩ := hm
    have he' : w' = P w := Subtype.ext he
    change f (P w) = 0
    exact LinearMap.mem_ker.mp (he' ▸ hw')
  let pJ := ((LinearMap.ker f).liftQ (f.comp P) hpKer).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hpJ (w : W) : pJ (f w) = f (P w) := by
    change (LinearMap.ker f).liftQ (f.comp P) hpKer
      ((f.quotKerEquivOfSurjective hf).symm (f w)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
    rfl
  let LM := Sum.elim (fun k => ρ k) L
  let LN := Sum.elim (fun k => ρ' k) L'
  let DM : K ⊕ ι → Module.End ℂ M := Sum.elim (fun _ => 0) D
  let DN : K ⊕ ι → Module.End ℂ N := Sum.elim (fun _ => 0) D'
  let H := (Option.elim · pJ (Sum.elim (fun k => ρJ k) LJ))
  let σ := FreeAlgebra.lift ℂ H
  have hj' : σ (FreeAlgebra.ι ℂ none) j ≠ 0 := by
    rw [FreeAlgebra.lift_ι_apply]
    change pJ j ≠ 0
    have he : P x = x := Subtype.ext hpFix
    rwa [← hx, hpJ, he, hx]
  have hsimp : IsSimple σ := isSimple_lift H fun U hU =>
    hirr U (fun k y hy => hU (some (.inl k)) y hy) (fun i y hy => hU (some (.inr i)) y hy)
  have hbase : IsConstituent (affineAction p LM DM 0) σ := by
    rw [affineAction_zero]
    apply isConstituent_lift
    have hw (i : Option (K ⊕ ι)) (y : M) (hy : y ∈ W) : i.elim p LM y ∈ W := by
      cases i with
      | none => exact hpMem WK y hy
      | some i => exact hW i y hy
    refine ⟨W, hw, f, hf, fun i y => ?_⟩
    cases i with
    | none => exact (hpJ y).symm
    | some i => exact heq i y
  have hgen (z : ℂ) (hz : z ∈ S) : ∃ e : M ≃ₗ[ℂ] N,
      (∀ y, e (p y) = q (e y)) ∧
      (∀ i y, e ((LM i + z • DM i) y) = (LN i + z • DN i) (e y)) := by
    obtain ⟨e, heK, heL⟩ := hiso z hz
    refine ⟨e, hpq e heK, fun i y => ?_⟩
    cases i with
    | inl k => simpa only [LM, LN, DM, DN, Sum.elim_inl, smul_zero, add_zero] using heK k y
    | inr i => exact heL i y
  have ht := isConstituent_of_affine_isomorphisms p q LM DM LN DN hS hgen 0 σ hbase hsimp hj'
  rw [affineAction_zero] at ht
  obtain ⟨V, hV, g, hg, hge⟩ := isOperatorConstituent_of_lift ht
  exact ⟨V, fun i => hV (some i), g, hg, fun i => hge (some i)⟩

end Langlands.Archimedean.ConstituentCompression
