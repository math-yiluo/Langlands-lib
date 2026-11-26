import Langlands.Correspondence.HenniartBaseChangeSlopeProof
import Langlands.VirtualRepresentation.Weil.Local
import Langlands.Correspondence.HenniartUnramified.Extension
import Langlands.Weil.Representation.InductionSemisimplicityProof
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-! # Weil representations across a cyclic prime-degree step -/

noncomputable section

namespace Langlands.Henniart.DescentWeil

open FiniteRepresentation FiniteRepresentation.SplitDegree Representation LinearMap

universe uG uQ uW uK

section Extension

variable {G : Type uG} {Q : Type uQ} [Group G] [Group Q]
variable {N : Subgroup G} [N.Normal]
variable {V : Type uW} [AddCommGroup V] [Module ℂ V]

/-- The pairs whose operator implements the indicated conjugation on the subgroup action. -/
private def compatibleOperators (ρ : Representation ℂ N V) :
    Subgroup (G × (Module.End ℂ V)ˣ) where
  carrier := {a | ∀ n, ρ.asGroupHom (MulAut.conjNormal a.1 n) =
    a.2 * ρ.asGroupHom n * a.2⁻¹}
  one_mem' := by intro n; simp
  mul_mem' {a b} ha hb := by
    intro n
    change ρ.asGroupHom (MulAut.conjNormal (a.1 * b.1) n) =
      (a.2 * b.2) * ρ.asGroupHom n * (a.2 * b.2)⁻¹
    rw [map_mul]
    change ρ.asGroupHom (MulAut.conjNormal a.1 (MulAut.conjNormal b.1 n)) = _
    rw [ha _, hb _]
    group
  inv_mem' {a} ha := by
    intro n
    have h := ha ((MulAut.conjNormal a.1)⁻¹ n)
    rw [MulAut.apply_inv_self] at h
    change ρ.asGroupHom (MulAut.conjNormal a.1⁻¹ n) = a.2⁻¹ * ρ.asGroupHom n * a.2⁻¹⁻¹
    rw [map_inv, h]
    group

private theorem covariant_asGroupHom (ρ : Representation ℂ N V) (n : N) :
    ((n : G), ρ.asGroupHom n) ∈ compatibleOperators ρ := by
  intro m
  rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv]

private theorem covariant_of_equiv (ρ : Representation ℂ N V) (a : G)
    (e : ρ.Equiv (ρ.comp (MulAut.conjNormal a).toMonoidHom)) :
    (a, GeneralLinearGroup.ofLinearEquiv e.toLinearEquiv) ∈ compatibleOperators ρ := by
  intro n
  apply Units.ext
  have h := e.isIntertwining' n
  change e.toLinearEquiv.toLinearMap * ρ n = ρ (MulAut.conjNormal a n) *
    e.toLinearEquiv.toLinearMap at h
  let B := GeneralLinearGroup.ofLinearEquiv e.toLinearEquiv
  change ρ (MulAut.conjNormal a n) = B.val * ρ n * B.inv
  change B.val * ρ n = ρ (MulAut.conjNormal a n) * B.val at h
  rw [h, mul_assoc, B.val_inv, mul_one]

/-- Extend a finite-dimensional irreducible representation across a finite cyclic quotient. -/
private theorem exists_extension [FiniteDimensional ℂ V] [Nontrivial V] [Finite Q] [IsCyclic Q]
    (q : G →* Q) (hq : Function.Surjective q) (ρ : Representation ℂ q.ker V)
    (hirr : ρ.IsIrreducible)
    (hconj : ∀ a : G, Nonempty (ρ.Equiv (ρ.comp (MulAut.conjNormal a).toMonoidHom))) :
    ∃ τ : Representation ℂ G V, τ.comp q.ker.subtype = ρ := by
  let d := Nat.card Q
  have hd : 0 < d := Nat.card_pos
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨a, rfl⟩ := hq b
  have ha : orderOf (q a) = d := orderOf_eq_card_of_forall_mem_zpowers hb
  let n : q.ker := ⟨a ^ d, by
    change q (a ^ d) = 1
    rw [map_pow, ← ha, pow_orderOf_eq_one]⟩
  let A := compatibleOperators ρ
  let U := GeneralLinearGroup.ofLinearEquiv (hconj a).some.toLinearEquiv
  have hU : (a, U) ∈ A := covariant_of_equiv ρ a (hconj a).some
  let C := (ρ.asGroupHom n)⁻¹ * U ^ d
  have hC : (1, C) ∈ A := by
    have h := A.mul_mem (A.inv_mem (covariant_asGroupHom ρ n)) (A.pow_mem hU d)
    change (((a ^ d)⁻¹ * a ^ d), C) ∈ A at h
    rwa [inv_mul_cancel] at h
  let T : ρ.IntertwiningMap ρ := ⟨C.val, fun m => by
    have h := hC m
    change ρ.asGroupHom (MulAut.conjNormal 1 m) = C * ρ.asGroupHom m * C⁻¹ at h
    rw [map_one] at h
    have hh := congrArg (fun u : (Module.End ℂ V)ˣ => (u * C).val) h
    simp only [MulAut.one_apply, mul_assoc, inv_mul_cancel, mul_one] at hh
    exact hh.symm⟩
  obtain ⟨c, hc⟩ := end_scalar ρ hirr T
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp [T] at hc
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ hd
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hd.ne'] at hz
    exact (inv_ne_zero hc0) hz.symm
  let scalar : ℂˣ →* (Module.End ℂ V)ˣ := Units.map (algebraMap ℂ _).toMonoidHom
  let u := Units.mk0 z hz0
  let t := Units.mk0 c hc0
  have hCscalar : C = scalar t := Units.ext (by simpa [scalar, t, Algebra.algebraMap_eq_smul_one, T] using hc)
  have hcentral (v : ℂˣ) (F : (Module.End ℂ V)ˣ) : Commute (scalar v) F := by
    apply Units.ext
    exact Algebra.commutes (R := ℂ) (A := Module.End ℂ V) (v : ℂ) F.val
  have hscalar : ((1 : G), scalar u) ∈ A := by
    intro m
    change ρ.asGroupHom (MulAut.conjNormal 1 m) = scalar u * ρ.asGroupHom m * (scalar u)⁻¹
    rw [map_one, MulAut.one_apply, (hcentral u (ρ.asGroupHom m)).eq, mul_assoc, mul_inv_cancel, mul_one]
  let B := scalar u * U
  have hB : (a, B) ∈ A := by
    simpa only [Prod.mul_def, one_mul, B] using A.mul_mem hscalar hU
  have hBpow : B ^ d = ρ.asGroupHom n := by
    have hut : u ^ d = t⁻¹ := Units.ext (by simpa [u, t] using hz)
    have hUeq : U ^ d = ρ.asGroupHom n * C := by simp [C]
    change (scalar u * U) ^ d = _
    rw [(hcentral u U).mul_pow, ← map_pow, hut, map_inv, hUeq, hCscalar,
      ← mul_assoc, (hcentral t (ρ.asGroupHom n)).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  let α : Multiplicative ℤ →* MulAut q.ker := MulAut.conjNormal.comp (zpowersHom G a)
  let L : (q.ker ⋊[α] (Multiplicative ℤ)) →* G :=
    SemidirectProduct.lift q.ker.subtype (zpowersHom G a) (fun i => by ext m; rfl)
  let D : (q.ker ⋊[α] (Multiplicative ℤ)) →* (Module.End ℂ V)ˣ :=
    SemidirectProduct.lift ρ.asGroupHom (zpowersHom _ B) (fun i => by
      ext m : 1
      exact (A.zpow_mem hB i.toAdd) m)
  have hL : Function.Surjective L := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hb (q g))
    let m : q.ker := ⟨g * (a ^ i)⁻¹, by
      change q (g * (a ^ i)⁻¹) = 1
      rw [map_mul, map_inv, map_zpow, hi, mul_inv_cancel]⟩
    refine ⟨⟨m, Multiplicative.ofAdd i⟩, ?_⟩
    change g * (a ^ i)⁻¹ * a ^ i = g
    group
  have hLD : L.ker ≤ D.ker := by
    intro x hx
    have hx' : (x.left : G) * a ^ x.right.toAdd = 1 := hx
    have hq' : q a ^ x.right.toAdd = 1 := by
      have h := congrArg q hx'
      rwa [map_mul, map_zpow, x.left.property, one_mul, map_one] at h
    obtain ⟨j, hj⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hq'
    rw [ha] at hj
    have hleft : x.left = (n ^ j)⁻¹ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_inv, Subgroup.coe_zpow, hj, zpow_mul, zpow_natCast,
        show (n : G) = a ^ d from rfl] using (eq_inv_of_mul_eq_one_left hx')
    change ρ.asGroupHom x.left * B ^ x.right.toAdd = 1
    rw [hleft, hj, zpow_mul, zpow_natCast, hBpow, map_inv, map_zpow, inv_mul_cancel]
  let e := QuotientGroup.quotientKerEquivOfSurjective L hL
  let τ := (Units.coeHom _).comp ((QuotientGroup.lift L.ker D hLD).comp e.symm.toMonoidHom)
  have hτ (x : q.ker ⋊[α] Multiplicative ℤ) : τ (L x) = (D x).val := by
    change ((QuotientGroup.lift L.ker D hLD) (e.symm (L x))).val = _
    have he : e.symm (L x) = QuotientGroup.mk x :=
      e.symm_apply_eq.mpr rfl
    rw [he]
    rfl
  refine ⟨τ, MonoidHom.ext fun m => ?_⟩
  change τ m = ρ m
  have hm : L (SemidirectProduct.inl m) = (m : G) := by simp [L]
  rw [← hm, hτ]
  simp only [D, SemidirectProduct.lift_inl, Representation.asGroupHom_apply]

end Extension

section Orbit

open scoped MonoidAlgebra
open Weil.InductionSemisimplicity (coind_semisimple)
open Induction (Cosets coordinates)

variable {G : Type uG} {Q : Type uQ} [Group G] [Group Q]
variable {N : Subgroup G} [N.Normal]
variable {V : Type uW} [AddCommGroup V] [Module ℂ V]

private theorem equiv_of_covariant (ρ : Representation ℂ N V) (g : G)
    {U : (Module.End ℂ V)ˣ} (hU : (g, U) ∈ compatibleOperators ρ) :
    Nonempty (ρ.Equiv (ρ.comp (MulAut.conjNormal g).toMonoidHom)) := by
  refine ⟨Representation.Equiv.mk (GeneralLinearGroup.toLinearEquiv U) fun n => ?_⟩
  have h := hU n
  change U.val * ρ n = ρ (MulAut.conjNormal g n) * U.val
  have h' := congrArg (fun u : (Module.End ℂ V)ˣ => (u * U).val) h
  rw [mul_assoc, inv_mul_cancel, mul_one] at h'
  exact h'.symm

/-- For a prime quotient, a class that moves has distinct conjugates at distinct cosets. -/
private theorem conjugates_distinct (q : G →* Q)
    [Fact (Nat.card Q).Prime] (ρ : Representation ℂ q.ker V)
    (hmove : ¬ ∀ g : G, Nonempty (ρ.Equiv (ρ.comp (MulAut.conjNormal g).toMonoidHom)))
    {g h : G} (hne : q g ≠ q h) :
    ¬ Nonempty (Representation.Equiv (ρ.comp (MulAut.conjNormal g).toMonoidHom)
      (ρ.comp (MulAut.conjNormal h).toMonoidHom)) := by
  let P := (compatibleOperators ρ).map (MonoidHom.fst G (Module.End ℂ V)ˣ)
  have hker : q.ker ≤ P := fun n hn => ⟨(n, ρ.asGroupHom ⟨n, hn⟩),
    covariant_asGroupHom ρ ⟨n, hn⟩, rfl⟩
  have hP : P.map q = ⊥ := by
    rcases (P.map q).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact hbot
    exfalso
    apply hmove
    intro a
    have hmem : q a ∈ P.map q := by rw [htop]; trivial
    obtain ⟨b, hb, hab⟩ := hmem
    have hba : b⁻¹ * a ∈ P := hker (by change q (b⁻¹ * a) = 1; rw [map_mul, map_inv, hab, inv_mul_cancel])
    have ha : a ∈ P := by simpa using P.mul_mem hb hba
    obtain ⟨⟨b, U⟩, hU, rfl⟩ := ha
    exact equiv_of_covariant ρ b hU
  rintro ⟨e⟩
  have e' : ρ.Equiv (ρ.comp (MulAut.conjNormal (h * g⁻¹)).toMonoidHom) := by
    have hl : (ρ.comp (MulAut.conjNormal g).toMonoidHom).comp
        (MulAut.conjNormal g⁻¹).toMonoidHom = ρ := by
      ext n : 1
      simp [map_inv]
    have hr : (ρ.comp (MulAut.conjNormal h).toMonoidHom).comp
        (MulAut.conjNormal g⁻¹).toMonoidHom =
        ρ.comp (MulAut.conjNormal (h * g⁻¹)).toMonoidHom := by
      ext n : 1
      simp [map_mul]
    have eh := equivComp e (MulAut.conjNormal g⁻¹).toMonoidHom
    rw [hl, hr] at eh
    exact eh
  have hmem : q (h * g⁻¹) ∈ P.map q :=
    ⟨_, ⟨_, covariant_of_equiv ρ _ e', rfl⟩, rfl⟩
  rw [hP, Subgroup.mem_bot, map_mul, map_inv, mul_inv_eq_one] at hmem
  exact hne hmem.symm

variable [N.FiniteIndex]

private def cosetBlock (A : FiniteRepresentation.{0, uG, uW} ℂ N) (i : Cosets N) :
    Representation ℂ N A := A.representation.comp (MulAut.conjNormal i.out).toMonoidHom

/-- The restriction of coinduction is block diagonal in coset coordinates. -/
private def coindRestrictEquiv (A : FiniteRepresentation.{0, uG, uW} ℂ N) :
    Representation.Equiv ((induce N A).representation.comp N.subtype) (blockRep (cosetBlock A)) :=
  Representation.Equiv.mk (coordinates N A) fun n => by
    apply LinearMap.ext
    intro f
    funext i
    change f.val (i.out * (n : G)) = A.representation (MulAut.conjNormal i.out n) (f.val i.out)
    have h := f.property (MulAut.conjNormal i.out n) i.out
    simpa only [Subgroup.coe_subtype, MulAut.conjNormal_apply, inv_mul_cancel_right] using h

/-- Coinduction of an irreducible representation with distinct coset conjugates is irreducible. -/
private theorem irreducible_coind (A : FiniteRepresentation.{0, uG, uW} ℂ N)
    (hA : A.IsIrreducible) (hApos : 0 < A.rank)
    (hdist : ∀ i j : Cosets N, i ≠ j → ¬ Nonempty ((cosetBlock A i).Equiv (cosetBlock A j))) :
    (induce N A).IsIrreducible := by
  classical
  let τ := (induce N A).representation
  let : Nontrivial A := Module.nontrivial_of_finrank_pos hApos
  have : Finite (Cosets N) := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel N).symm
  let : Fintype (Cosets N) := Fintype.ofFinite _
  let : Nonempty (Cosets N) := ⟨Induction.coset N 1⟩
  let : Nontrivial (induce N A : Type (max uG uW)) :=
    (coordinates N A).symm.injective.nontrivial
  have blockIrr (i : Cosets N) : (cosetBlock A i).IsIrreducible :=
    isIrreducible_comp_surjective A.representation _ (MulAut.conjNormal i.out).surjective hA
  have endScalar (T : τ.IntertwiningMap τ) : ∃ c : ℂ, ∀ f, T f = c • f := by
    let e := coindRestrictEquiv A
    let T' : Representation.IntertwiningMap (τ.comp N.subtype) (τ.comp N.subtype) :=
      ⟨T.toLinearMap, fun n => T.isIntertwining' n⟩
    let B := e.toIntertwiningMap.comp (T'.comp e.symm.toIntertwiningMap)
    have hd (i j : Cosets N) (hij : i ≠ j)
        (F : (cosetBlock A i).IntertwiningMap (cosetBlock A j)) : F = 0 := by
      by_contra hF
      exact hdist i j hij (nonempty_equiv_of_ne_zero _ _ (blockIrr i) (blockIrr j) F hF)
    obtain ⟨c, hc⟩ := blockRep_endo_diag (cosetBlock A) blockIrr hd B.toLinearMap B.isIntertwining'
    have hcoord (f : induce N A) (i : Cosets N) : (T f).val i.out = c i • f.val i.out := by
      have h := hc (e f) i
      change e (T (e.symm (e f))) i = _ at h
      rw [e.symm_apply_apply] at h
      exact h
    let i := Induction.coset N 1
    refine ⟨c i, fun f => Subtype.ext (funext fun g => ?_)⟩
    let a := i.out⁻¹ * g
    have h := hcoord (τ a f) i
    rw [T.isIntertwining] at h
    change (T f).val (i.out * a) = c i • f.val (i.out * a) at h
    change (T f).val g = c i • f.val g
    simpa only [a, mul_inv_cancel_left] using h
  let : A.representation.IsIrreducible := hA
  have hss := coind_semisimple N A.representation (inferInstance : IsSemisimpleRepresentation A.representation)
  let : IsSemisimpleModule ℂ[G] τ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule τ).mp hss
  let : Nontrivial τ.asModule := inferInstanceAs (Nontrivial (induce N A : Type (max uG uW)))
  refine (irreducible_iff_isSimpleModule_asModule τ).mpr ?_
  refine { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩, eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨U, hU⟩ := exists_isCompl W
  let proj := W.projection U hU
  let T := (IntertwiningMap.equivLinearMapAsModule τ τ).symm proj
  obtain ⟨c, hc⟩ := endScalar T
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hw' := hc w
  change proj w = c • w at hw'
  rw [Submodule.projection_apply_left hU ⟨w, hw⟩] at hw'
  have hc1 : c = 1 := smul_left_injective ℂ hw0 (hw'.symm.trans (one_smul ℂ w).symm)
  apply eq_top_iff.mpr
  intro f _
  have hf := hc f
  change proj f = c • f at hf
  rw [hc1, one_smul] at hf
  rw [← hf]
  exact Submodule.projection_apply_mem hU f

end Orbit

section QuotientTwists

variable {G : Type uG} {Q : Type uQ} [Group G] [Group Q]
variable {V : Type uW} [AddCommGroup V] [Module ℂ V]

private theorem twist_restrict_ker (q : G →* Q) (χ : Q →* ℂˣ) (τ : Representation ℂ G V) :
    (Langlands.twist (χ.comp q) τ).comp q.ker.subtype = τ.comp q.ker.subtype := by
  ext n : 1
  change (χ (q n) : ℂ) • τ n = τ n
  rw [show q n = 1 from n.property, map_one, Units.val_one, one_smul]

/-- If the restriction is irreducible, distinct quotient characters give distinct twists. -/
private theorem quotient_twists_injective [FiniteDimensional ℂ V] [Nontrivial V]
    (q : G →* Q) (hq : Function.Surjective q) (τ : Representation ℂ G V)
    (hirr : Representation.IsIrreducible (τ.comp q.ker.subtype)) :
    Function.Injective (fun χ : Q →* ℂˣ => classOf (of (Langlands.twist (χ.comp q) τ))) := by
  intro χ η he
  obtain ⟨e⟩ := (classOf_eq_iff _ _).mp he
  let T : IntertwiningMap (τ.comp q.ker.subtype) (τ.comp q.ker.subtype) :=
    ⟨e.toLinearEquiv.toLinearMap, fun n => by
      have h := e.isIntertwining' (n : G)
      change e.toLinearEquiv.toLinearMap ∘ₗ ((χ (q n) : ℂ) • τ n) =
        ((η (q n) : ℂ) • τ n) ∘ₗ e.toLinearEquiv.toLinearMap at h
      change e.toLinearEquiv.toLinearMap ∘ₗ τ n = τ n ∘ₗ e.toLinearEquiv.toLinearMap
      simpa only [show q n = 1 from n.property, map_one, Units.val_one, one_smul] using h⟩
  obtain ⟨c, hc⟩ := end_scalar _ hirr T
  have he' (v : V) : e v = c • v := LinearMap.congr_fun hc v
  ext b
  obtain ⟨g, rfl⟩ := hq b
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h := LinearMap.congr_fun (e.isIntertwining' g) v
  change e ((χ (q g) : ℂ) • τ g v) = (η (q g) : ℂ) • τ g (e v) at h
  have hcomm : e (τ g v) = τ g (e v) := by rw [he', he', map_smul]
  rw [map_smul, hcomm] at h
  have hnonzero : τ g (e v) ≠ 0 := by
    intro h0
    have hh := congrArg (τ g⁻¹) h0
    rw [Representation.inv_self_apply, map_zero] at hh
    exact hv (e.injective (hh.trans e.toLinearEquiv.map_zero.symm))
  exact smul_left_injective ℂ hnonzero h

end QuotientTwists

section Local

open Numerical Correspondence Weil.Local

variable {p : ℕ} [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)

private abbrev quotientMap : localWeilGroup S.base →* S.Gal :=
  (finiteGaloisQuotient S.base S.top S.embedding S.isGalois).toMonoidHom

private abbrev kernelEquiv : localWeilGroup S.top ≃ₜ* (quotientMap S).ker :=
  finiteGaloisQuotientKernelEquiv S.base S.top S.embedding S.isGalois

private theorem kernel_open : IsOpen ((quotientMap S).ker : Set (localWeilGroup S.base)) := by
  rw [finiteGaloisQuotient_ker]
  exact (extensionWeilMap_isOpenEmbedding S.base S.top S.embedding).isOpen_range

private theorem quotient_surjective : Function.Surjective (quotientMap S) :=
  finiteGaloisQuotient_surjective S.base S.top S.embedding S.isGalois

private theorem restriction_continuous {V : Type uW} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (τ : Representation ℂ (localWeilGroup S.base) V)
    (hc : (of (τ.comp (quotientMap S).ker.subtype)).IsContinuous) : (of τ).IsContinuous := by
  let : TopologicalSpace (Module.End ℂ V) := moduleTopology ℂ _
  have : IsModuleTopology ℂ (Module.End ℂ V) := ⟨rfl⟩
  have : IsTopologicalRing (Module.End ℂ V) := IsModuleTopology.isTopologicalRing ℂ _
  have hOn : ContinuousOn τ ((quotientMap S).ker : Set _) :=
    continuousOn_iff_continuous_domRestrict.mpr hc
  exact continuous_of_continuousAt_one τ (hOn.continuousAt
    ((kernel_open S).mem_nhds ((quotientMap S).ker.one_mem)))

private theorem conj_through_kernel (w : localWeilGroup S.base) (n : (quotientMap S).ker) :
    finiteGaloisWeilConjugation S.base S.top S.embedding S.isGalois w ((kernelEquiv S).symm n) =
      (kernelEquiv S).symm (MulAut.conjNormal w n) := by
  apply (extensionWeilMap_injective S.base S.top S.embedding)
  rw [extensionWeilMap_finiteGaloisWeilConjugation,
    extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm,
    extensionWeilMap_finiteGaloisQuotientKernelEquiv_symm, MulAut.conjNormal_apply]

private theorem rep_of_class {j : ℕ} (T : IrreducibleWeilClass.{uK, uW} S.top j.succPNat) :
    ∃ (A : LocalWeilRepresentation.{uK, uW} S.top) (hc : A.IsContinuous) (hi : A.IsIrreducible)
      (hr : A.rank = j + 1),
      T = (VirtualRepresentation.LocalWeil.basisClass A hc hi j.succPNat hr).2 := by
  obtain ⟨c, hr⟩ := T
  obtain ⟨A, rfl⟩ := Quotient.exists_rep c
  exact ⟨A.val, A.property.1, A.property.2, hr, rfl⟩

private theorem weilConjugate_eq_iff {j : ℕ} (A : LocalWeilRepresentation.{uK, uW} S.top)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (hr : A.rank = j + 1)
    (w : localWeilGroup S.base) :
    let T := (VirtualRepresentation.LocalWeil.basisClass A hc hi j.succPNat hr).2
    let B := restrict (kernelEquiv S).symm.toMonoidHom A
    weilConjugate S w T = T ↔
      Nonempty (Representation.Equiv B.representation
        (B.representation.comp (MulAut.conjNormal w).toMonoidHom)) := by
  dsimp only
  let f := finiteGaloisWeilConjugation S.base S.top S.embedding S.isGalois w
  let E := kernelEquiv S
  let B := restrict E.symm.toMonoidHom A
  have hrw : (A.representation.comp f.toMonoidHom).comp E.symm.toMonoidHom =
      B.representation.comp (MulAut.conjNormal w).toMonoidHom := by
    ext n : 1
    change A.representation (f (E.symm n)) = A.representation (E.symm (MulAut.conjNormal w n))
    rw [conj_through_kernel]
  let T := (VirtualRepresentation.LocalWeil.basisClass A hc hi j.succPNat hr).2
  have hForget : weilConjugate S w T = T ↔ classOf (restrict f.toMonoidHom A) = classOf A := by
    constructor
    · intro he
      exact congrArg (weilClassForget S.top) he
    · intro he
      exact Subtype.ext (forgetPropertyClass_injective _ he)
  rw [hForget, classOf_eq_iff]
  constructor
  · rintro ⟨e⟩
    have he := equivComp e.symm E.symm.toMonoidHom
    change Representation.Equiv B.representation
      ((A.representation.comp f.toMonoidHom).comp E.symm.toMonoidHom) at he
    rw [hrw] at he
    exact ⟨he⟩
  · rintro ⟨e⟩
    have he : Representation.Equiv (A.representation.comp E.symm.toMonoidHom)
        ((A.representation.comp f.toMonoidHom).comp E.symm.toMonoidHom) := hrw ▸ e
    refine ⟨(Representation.Equiv.mk he.toLinearEquiv fun n => ?_).symm⟩
    have hh := he.isIntertwining' (E n)
    change he.toLinearEquiv.toLinearMap ∘ₗ A.representation (E.symm (E n)) =
      A.representation (f (E.symm (E n))) ∘ₗ he.toLinearEquiv.toLinearMap at hh
    rw [ContinuousMulEquiv.symm_apply_apply] at hh
    exact hh

/-- An invariant Weil class in a cyclic prime step has a family of distinct extensions
indexed by the degree of the step. -/
theorem extensions (k : ℕ) (T : IrreducibleWeilClass.{uK, uW} S.top k.succPNat)
    (hfix : ∀ w, weilConjugate S w T = T) :
    ∃ f : Fin S.degree → IrreducibleWeilClass.{uK, uW} S.base k.succPNat,
      Function.Injective f ∧ ∀ i,
        extensionRestrictClass S.base S.top S.embedding (weilClassForget S.base (f i)) =
          weilClassForget S.top T := by
  classical
  have : Finite S.Gal := S.finite_gal
  have : Fact (Nat.card S.Gal).Prime := ⟨S.card_prime⟩
  have : IsCyclic S.Gal := isCyclic_of_prime_card rfl
  let : CommGroup S.Gal := IsCyclic.commGroup
  obtain ⟨A, hc, hi, hr, rfl⟩ := rep_of_class S T
  let E := kernelEquiv S
  let B := restrict E.symm.toMonoidHom A
  let : Nontrivial B := by
    change Nontrivial A
    exact Module.nontrivial_of_finrank_eq_succ hr
  have hB : B.IsIrreducible := (isIrreducible_restrict_iff E.symm.toMonoidHom E.symm.surjective A).mpr hi
  have hcB : B.IsContinuous := isContinuous_restrict _ E.symm.continuous hc
  obtain ⟨τ, hτ⟩ := exists_extension (quotientMap S) (quotient_surjective S) B.representation hB
    (fun w => (weilConjugate_eq_iff S A hc hi hr w).mp (hfix w))
  let q := quotientMap S
  let χGroup := S.Gal →* ℂˣ
  have hD : Nat.card S.Gal ≠ 0 := S.card_prime.ne_zero
  let : NeZero (Nat.card S.Gal) := ⟨hD⟩
  let : HasEnoughRootsOfUnity ℂ (Nat.card S.Gal) :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp _ hD⟩, rootsOfUnity.isCyclic _ _⟩
  let e : χGroup ≃ Fin S.degree := (IsCyclic.monoidHom_equiv_self S.Gal ℂ).some.toEquiv.trans
    (Finite.equivFinOfCardEq S.degree_eq_card.symm)
  let τχ (χ : χGroup) := Langlands.twist (χ.comp q) τ
  have hres (χ : χGroup) : (τχ χ).comp q.ker.subtype = B.representation :=
    (twist_restrict_ker q χ τ).trans hτ
  have hci (χ : χGroup) : (of (τχ χ)).IsContinuous := restriction_continuous S _ (by
    change (of ((τχ χ).comp q.ker.subtype)).IsContinuous
    rw [hres]
    exact hcB)
  have hii (χ : χGroup) : (of (τχ χ)).IsIrreducible :=
    isIrreducible_of_comp _ q.ker.subtype (by rw [hres]; exact hB)
  let f (i : Fin S.degree) : IrreducibleWeilClass.{uK, uW} S.base k.succPNat :=
    (VirtualRepresentation.LocalWeil.basisClass (of (τχ (e.symm i)))
      (hci _) (hii _) k.succPNat hr).2
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    exact quotient_twists_injective q (quotient_surjective S) τ (by rw [hτ]; exact hB)
      (congrArg (weilClassForget S.base) hij)
  · intro i
    change classOf (extensionRestrict S.base S.top S.embedding (of (τχ (e.symm i)))) = classOf A
    apply (classOf_eq_iff _ _).mpr
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun w => ?_⟩
    have h := DFunLike.congr_fun (hres (e.symm i)) (E w)
    change τχ (e.symm i) (extensionWeilMap S.base S.top S.embedding w) =
      A.representation (E.symm (E w)) at h
    rw [ContinuousMulEquiv.symm_apply_apply] at h
    exact h

/-- The coinduction of a moving Weil class has the prime-degree family of conjugates
as its restriction. The finite coset coordinates keep the carrier in the input universe. -/
theorem induction (k j : ℕ) (T : IrreducibleWeilClass.{uK, uW} S.top j.succPNat)
    (hrank : k + 1 = (j + 1) * S.degree) (hmove : ¬ ∀ w, weilConjugate S w T = T) :
    ∃ (σ : IrreducibleWeilClass.{uK, uW} S.base k.succPNat)
      (m : Multiset (Σ a : ℕ, IrreducibleWeilClass.{uK, uW} S.top a.succPNat)),
      IsRestrictionDecomposition S σ m ∧ ⟨j, T⟩ ∈ m ∧
        m.card = S.degree ∧ ∀ t ∈ m, t.1 = j := by
  classical
  let q := quotientMap S
  let N := q.ker
  let E := kernelEquiv S
  have hindex : N.index = S.degree :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q (quotient_surjective S)).toEquiv).trans
      S.degree_eq_card.symm
  let : N.FiniteIndex := Subgroup.finiteIndex_iff.mpr (hindex.trans_ne S.degree_prime.ne_zero)
  have : Fact (Nat.card S.Gal).Prime := ⟨S.card_prime⟩
  obtain ⟨A, hc, hi, hr, rfl⟩ := rep_of_class S T
  let B := restrict E.symm.toMonoidHom A
  have hiB : B.IsIrreducible := (isIrreducible_restrict_iff E.symm.toMonoidHom E.symm.surjective A).mpr hi
  have hcB : B.IsContinuous := isContinuous_restrict _ E.symm.continuous hc
  have hm : ¬ ∀ w : localWeilGroup S.base, Nonempty (Representation.Equiv B.representation
      (B.representation.comp (MulAut.conjNormal w).toMonoidHom)) :=
    fun h => hmove fun w => (weilConjugate_eq_iff S A hc hi hr w).mpr (h w)
  let C := induce N B
  have hiC : C.IsIrreducible := irreducible_coind B hiB (by change 0 < A.rank; rw [hr]; omega) (by
    intro a b hab
    apply conjugates_distinct q B.representation hm
    intro h
    apply hab
    rw [← Induction.coset_out N a, ← Induction.coset_out N b]
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    change q (b.out * a.out⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel])
  have hcC : C.IsContinuous := isContinuous_induce N (kernel_open S) hcB
  let cosetEquiv := QuotientGroup.quotientRightRelEquivQuotientLeftRel N
  have : Finite (Induction.Cosets N) := Finite.of_equiv _ cosetEquiv.symm
  have hcard : Nat.card (Induction.Cosets N) = S.degree := (Nat.card_congr cosetEquiv).trans hindex
  let e : Fin S.degree ≃ Induction.Cosets N := (Finite.equivFinOfCardEq hcard).symm
  let c := Induction.coordinates N B
  let coord : C ≃ₗ[ℂ] (Fin S.degree → A) := c.trans (LinearEquiv.funCongrLeft ℂ A e)
  let D : LocalWeilRepresentation.{uK, uW} S.base := of (coord.conjRingEquiv.toMonoidHom.comp C.representation)
  let eD : FiniteRepresentation.Equiv C D := Representation.Equiv.mk coord fun g => by
    apply LinearMap.ext
    intro v
    change coord (C.representation g v) = coord (C.representation g (coord.symm (coord v)))
    rw [coord.symm_apply_apply]
  have hrD : D.rank = k + 1 := by
    rw [← rank_eq_of_equiv eD, rank_induce, hindex, rank_restrict, hr, hrank, mul_comm]
  have hiD : D.IsIrreducible := (Weil.IsomorphismInvariance.irreducible_iff eD).mp hiC
  have hcD : D.IsContinuous := Weil.IsomorphismInvariance.continuous_of_equiv eD hcC
  let σ := (VirtualRepresentation.LocalWeil.basisClass D hcD hiD k.succPNat hrD).2
  let T := (VirtualRepresentation.LocalWeil.basisClass A hc hi j.succPNat hr).2
  let t (i : Fin S.degree) : Σ a : ℕ, IrreducibleWeilClass.{uK, uW} S.top a.succPNat :=
    ⟨j, weilConjugate S (e i).out T⟩
  let l := List.ofFn t
  have hlen : l.length = S.degree := List.length_ofFn
  let a (i : Fin l.length) := e (Fin.cast hlen i)
  let R (i : Fin l.length) := restrict
    (finiteGaloisWeilConjugation S.base S.top S.embedding S.isGalois (a i).out).toMonoidHom A
  refine ⟨σ, l, ⟨l, rfl, ?_⟩, ?_, hlen, ?_⟩
  · have hrClass : (fun i : Fin l.length => weilClassForget S.top (l.get i).2) =
        fun i => classOf (R i) := by
      funext i
      change weilClassForget S.top ((List.ofFn t).get i).2 = _
      rw [List.get_ofFn]
      rfl
    rw [hrClass, directSumClass_classOf]
    let f := (extensionWeilMap S.base S.top S.embedding).toMonoidHom
    change classOf (restrict f D) = classOf (directSum R)
    let esum := DirectSum.linearEquivFunOnFintype ℂ (Fin l.length) (fun i => R i)
    let reindex := LinearEquiv.funCongrLeft ℂ A ((finCongr hlen).trans e)
    let er : FiniteRepresentation.Equiv (restrict f C) (directSum R) :=
      Representation.Equiv.mk ((c.trans reindex).trans esum.symm) fun w => by
        apply LinearMap.ext
        intro v
        change (C : Type (max uK uW)) at v
        apply esum.injective
        funext i
        change (c (C.representation (f w) v)) (a i) =
          DirectSum.lmap (fun j => (R j).representation w) (esum.symm (reindex (c v))) i
        rw [DirectSum.lmap_apply]
        change (c (C.representation (f w) v)) (a i) =
          (R i).representation w (esum (esum.symm (reindex (c v))) i)
        have hx := congrFun (esum.apply_symm_apply (reindex (c v))) i
        have h := congrFun (LinearMap.congr_fun ((coindRestrictEquiv B).isIntertwining' (E w)) v) (a i)
        change (c (C.representation (f w) v)) (a i) =
          A.representation (E.symm (MulAut.conjNormal (a i).out (E w))) (c v (a i)) at h
        rw [← conj_through_kernel, ContinuousMulEquiv.symm_apply_apply] at h
        exact h.trans (congrArg ((R i).representation w) hx.symm)
    exact (classOf_eq_iff _ _).mpr ⟨(equivComp eD.symm f).trans er⟩
  · apply Multiset.mem_coe.mpr
    apply (List.mem_ofFn' _ _).mpr
    let i := Induction.coset N 1
    have hn : i.out ∈ N := by
      have h := QuotientGroup.rightRel_apply.mp (Quotient.exact i.out_eq)
      change (1 : localWeilGroup S.base) * i.out⁻¹ ∈ N at h
      rw [one_mul] at h
      exact N.inv_mem_iff.mp h
    refine ⟨e.symm i, ?_⟩
    change t (e.symm i) = _
    dsimp only [t]
    rw [e.apply_symm_apply]
    apply congrArg (Sigma.mk (β := fun a : ℕ => IrreducibleWeilClass.{uK, uW} S.top a.succPNat) j)
    exact (weilConjugate_eq_iff S A hc hi hr i.out).mpr
      (equiv_of_covariant B.representation i.out (covariant_asGroupHom B.representation ⟨i.out, hn⟩))
  · intro τ hτ
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp (Multiset.mem_coe.mp hτ)
    rfl

end Local

end Langlands.Henniart.DescentWeil
