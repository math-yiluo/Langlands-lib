import Langlands.Cohomology.Profinite.Dimension.Basic
import Langlands.Cohomology.Profinite.Finiteness
import Langlands.Cohomology.Profinite.Duality.DualModule
import Langlands.Cohomology.Profinite.EulerCharacteristic
import Langlands.Cohomology.Profinite.TorsionDual
import Langlands.GaloisCohomology.Field.KummerSequence
import Langlands.GaloisCohomology.Local.Arithmetic.Powers
import Langlands.GaloisCohomology.Local.ClassFormation
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Additive

/-!
# Finiteness of the cohomology of a local field in degrees `≤ 2`

For a nonarchimedean local field `K`, a separable closure `Ksep`, an open subgroup `U` of
`Gal(Ksep/K)` and a finite smooth module `M` of `U` killed by an integer `n` invertible in `K`,
the groups `Hʳ(U, M)` are finite for `r ≤ 2`.

The proof: for `μ_n` from the Kummer sequence (`H¹(U, μ_n)` is a quotient of `Eˣ/Eˣⁿ` for the fixed
field `E` of `U`, finite by `finite_quotient_range_powMonoidHom`; `H²(U, μ_n)` injects into the
`n`-torsion of `H²(U, Ksepˣ) ≅ ℚ/ℤ`); then for modules with trivial action of an open subgroup
that fixes `μ_n`, by induction on the order, through sub-modules `ℤ/p ≅ μ_p`; finally for all
modules by dévissage through the coinduced module of an open subgroup acting trivially
(`finite_cohomology_of_forall_trivial` of `Langlands.Cohomology.Profinite.Finiteness`, Shapiro's
lemma).
-/

noncomputable section

open CategoryTheory Limits

universe u

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology ClassFieldTheory.Local IntermediateField

section Res

/-- The restriction of `μ_n` to a subgroup is smooth (instance search does not find it through
`isSmoothRep_res_subtype`, because `rootsOfUnityModule` unfolds to `Rep.of`). -/
instance isSmoothRep_res_rootsOfUnityModule (K : Type*) (L : Type u) [Field K] [Field L]
    [Algebra K L] [Algebra.IsIntegral K L] (n : ℕ) (W : Subgroup Gal(L/K)) :
    IsSmoothRep (Rep.res W.subtype (rootsOfUnityModule K L n)) :=
  isSmoothRep_res_subtype _ _

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (n : ℕ)
  (V : Subgroup Gal(Ksep/K))

/-- The Kummer sequence restricted to a subgroup `V` of `Gal(Ksep/K)`, with its three terms
written as restrictions. -/
abbrev kummerSequenceRes : ShortComplex (Rep.{u} (ULift.{u} ℤ) V) where
  X₁ := Rep.res V.subtype (rootsOfUnityModule K Ksep n)
  X₂ := Rep.res V.subtype (unitsModule K Ksep)
  X₃ := Rep.res V.subtype (unitsModule K Ksep)
  f := (Rep.resFunctor V.subtype).map (kummerSequence K Ksep n).f
  g := (Rep.resFunctor V.subtype).map (kummerSequence K Ksep n).g
  zero := ((kummerSequence K Ksep n).map (Rep.resFunctor V.subtype)).zero

instance isSmoothRep_kummerSequenceRes_X₁ : IsSmoothRep (kummerSequenceRes (K := K) n V).X₁ :=
  isSmoothRep_res_subtype _ _

instance isSmoothRep_kummerSequenceRes_X₂ : IsSmoothRep (kummerSequenceRes (K := K) n V).X₂ :=
  isSmoothRep_res_subtype _ _

instance isSmoothRep_kummerSequenceRes_X₃ : IsSmoothRep (kummerSequenceRes (K := K) n V).X₃ :=
  isSmoothRep_res_subtype _ _

theorem kummerSequenceRes_shortExact (hn : (n : K) ≠ 0) :
    (kummerSequenceRes (K := K) (Ksep := Ksep) n V).ShortExact :=
  shortExact_map_res V (kummerSequence_shortExact n hn)

theorem cohomologyMap_kummerSequenceRes_g_apply (i : ℕ)
    (y : cohomology (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₂ i) :
    (coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).g i).hom y = n • y := by
  have h : (kummerSequenceRes (K := K) (Ksep := Ksep) n V).g =
      n • 𝟙 (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₂ := by
    ext x
    exact (nsmul_id_hom_apply _ n x).trans (nsmul_id_hom_apply _ n x).symm
  rw [h]
  exact cohomologyMap_nsmul_id_apply _ n i y

end Res

namespace Local

section Kummer

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ} (hn : (n : K) ≠ 0)
  (V : OpenSubgroup Gal(Ksep/K))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem subsingleton_cohomology_one_res_unitsModule :
    Subsingleton (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (unitsModule K Ksep)) 1) :=
  ModuleCat.isZero_iff_subsingleton.1 (isZero_cohomology_one_res_unitsModule V)

include hn in
/-- `H¹(V, μ_n)` is finite for an open subgroup `V`: it is a quotient of `Eˣ/Eˣⁿ` for the fixed
field `E` of `V` (Kummer theory). -/
theorem finite_cohomology_one_res_rootsOfUnityModule :
    Finite (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep n)) 1) := by
  let E := IntermediateField.fixedField (V : Subgroup Gal(Ksep/K))
  let S := kummerSequenceRes (K := K) (Ksep := Ksep) n (V : Subgroup Gal(Ksep/K))
  have hS : S.ShortExact := kummerSequenceRes_shortExact n _ hn
  have h1 : Subsingleton (cohomology S.X₂ 1) := subsingleton_cohomology_one_res_unitsModule K Ksep V
  have hfix : ∀ (u : Eˣ) (σ : (V : Subgroup Gal(Ksep/K))),
      S.X₃.ρ σ (Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) u)) =
        Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) u) := fun u σ =>
    congrArg Additive.ofMul
      (Units.ext ((IntermediateField.mem_fixedField_iff _ _).1 (u : E).2 σ σ.2))
  let φ : Additive Eˣ →+ S.X₃.ρ.invariants :=
    { toFun := fun u => ⟨Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) u.toMul),
        (Representation.mem_invariants _ _).2 (hfix u.toMul)⟩
      map_zero' := Subtype.ext (by
        change Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) 1) =
          Additive.ofMul (1 : Ksepˣ)
        rw [map_one])
      map_add' := fun a b => Subtype.ext (by
        change Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) (a.toMul * b.toMul)) =
          Additive.ofMul (Units.map (algebraMap E Ksep : E →* Ksep) a.toMul *
            Units.map (algebraMap E Ksep : E →* Ksep) b.toMul)
        rw [map_mul]) }
  let ψ : Additive Eˣ →+ cohomology S.X₁ 1 :=
    (δ hS 0 1 rfl).hom.toAddMonoidHom.comp ((zeroIso S.X₃).inv.hom.toAddMonoidHom.comp φ)
  have hsurj : Function.Surjective ψ := fun x => by
    obtain ⟨v, hv⟩ := exists_δ_zeroIso_inv_eq hS h1 x
    have ha : ((Additive.toMul (α := Ksepˣ) v.1 : Ksepˣ) : Ksep) ∈ E :=
      (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ =>
        congrArg (fun y : Additive Ksepˣ => ((Additive.toMul y : Ksepˣ) : Ksep))
          ((Representation.mem_invariants _ _).1 v.2 ⟨σ, hσ⟩)
    let u : Eˣ := Units.mk0 ⟨_, ha⟩ fun h =>
      (Additive.toMul (α := Ksepˣ) v.1 : Ksepˣ).ne_zero (congrArg Subtype.val h)
    have hu : φ (Additive.ofMul u) = v := Subtype.ext (congrArg Additive.ofMul (Units.ext rfl))
    refine ⟨Additive.ofMul u, ?_⟩
    change (δ hS 0 1 rfl).hom ((zeroIso S.X₃).inv.hom (φ (Additive.ofMul u))) = x
    rw [hu, hv]
  have hker : ∀ u : Additive Eˣ, ψ (n • u) = 0 := fun u => by
    change (δ hS 0 1 rfl).hom ((zeroIso S.X₃).inv.hom (φ (n • u))) = 0
    rw [map_nsmul]
    refine (δ_zeroIso_inv_eq_zero_iff hS (n • φ u)).2 ⟨φ u, Subtype.ext ?_⟩
    exact nsmul_id_hom_apply (unitsModule K Ksep) n _
  have hmE : ((n : ℕ) : E) ≠ 0 := by
    rw [← map_natCast (algebraMap K E) n]
    exact (map_ne_zero_iff _ (algebraMap K E).injective).2 hn
  let := LocalField.FiniteExtension.normedField K E
  let := LocalField.FiniteExtension.valuativeRel K E
  let := LocalField.FiniteExtension.isLocalField K E
  have hfinE : Finite (Eˣ ⧸ (powMonoidHom n : Eˣ →* Eˣ).range) :=
    finite_quotient_range_powMonoidHom (K := E) hmE
  let ψm : Eˣ →* Multiplicative (cohomology S.X₁ 1) := AddMonoidHom.toMultiplicativeRight ψ
  have hle : (powMonoidHom n : Eˣ →* Eˣ).range ≤ ψm.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    change Multiplicative.ofAdd (ψ (Additive.ofMul (u ^ n))) = 1
    rw [ofMul_pow, hker]
    rfl
  refine Finite.of_surjective (fun q => Multiplicative.toAdd (QuotientGroup.lift _ ψm hle q))
    fun x => ?_
  obtain ⟨u, rfl⟩ := hsurj x
  refine ⟨QuotientGroup.mk (Additive.toMul u), ?_⟩
  change Multiplicative.toAdd (QuotientGroup.lift _ ψm hle (QuotientGroup.mk (Additive.toMul u))) =
    ψ u
  rw [QuotientGroup.lift_mk]
  rfl

include hn in
/-- `H²(V, μ_n)` is finite: it injects into the `n`-torsion of `H²(V, Ksepˣ) ≅ ℚ/ℤ`. -/
theorem finite_cohomology_two_res_rootsOfUnityModule :
    Finite (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep n)) 2) := by
  set F := classFormation K Ksep
  have hS := kummerSequenceRes_shortExact (Ksep := Ksep) n (V : Subgroup Gal(Ksep/K)) hn
  have hinj := cohomologyMap_f_injective_of_subsingleton hS 1
    (subsingleton_cohomology_one_res_unitsModule K Ksep V)
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by simp [h])
  have htors : ∀ x : cohomology (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₁ 2,
      F.inv V ((coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).f 2).hom x) ∈
        {q : QZ | n • q = 0} := fun x => by
    have e : n • (coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).f 2).hom x = 0 := by
      rw [← cohomologyMap_kummerSequenceRes_g_apply]
      exact cohomologyMap_g_cohomologyMap_f_apply 2 x
    exact ((F.inv V).map_nsmul n _).symm.trans ((congrArg (F.inv V) e).trans (F.inv V).map_zero)
  have := (QZ.finite_setOf_nsmul_eq_zero hn0).to_subtype
  exact Finite.of_injective (fun x => (⟨_, htors x⟩ : {q : QZ | n • q = 0}))
    fun x y h => hinj ((F.inv_bijective V).1 (congrArg Subtype.val h))

include hn in
/-- `H³(V, μ_n) = 0` when `H³(V, Ksepˣ) = 0`. -/
theorem subsingleton_cohomology_three_res_rootsOfUnityModule :
    Subsingleton (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep n)) 3) := by
  set F := classFormation K Ksep
  have h3 := subsingleton_cohomology_res_unitsModule_of_three_le K Ksep V (le_refl 3)
  have hS := kummerSequenceRes_shortExact (Ksep := Ksep) n (V : Subgroup Gal(Ksep/K)) hn
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  suffices h : ∀ x : cohomology (kummerSequenceRes (K := K) (Ksep := Ksep) n V).X₁ 3, x = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (cohomology_exact₁ hS 2 3 rfl) x
    (h3.elim _ _)
  obtain ⟨q, hq⟩ := QZ.exists_nsmul_eq hn0 (F.inv V z)
  obtain ⟨w, hw⟩ := (F.inv_bijective V).2 q
  have hzw : z = (coeffMap (kummerSequenceRes (K := K) (Ksep := Ksep) n V).g 2).hom w := by
    apply (F.inv_bijective V).1
    refine hq.symm.trans ?_
    rw [← hw, ← map_nsmul]
    exact congrArg (F.inv V)
      (cohomologyMap_kummerSequenceRes_g_apply n (V : Subgroup Gal(Ksep/K)) 2 w).symm
  rw [← hz, hzw]
  exact congrArg (fun φ => φ.hom w) (comp_δ hS 2 3 rfl)

include hn in
theorem finite_cohomology_res_rootsOfUnityModule (r : ℕ) (hr : r ≤ 2) :
    Finite (cohomology (Rep.res (V : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep n)) r) := by
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  have : NeZero n := ⟨hn0⟩
  have : Finite (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity n Ksep)))
  interval_cases r
  · exact finite_cohomology_zero _
  · exact finite_cohomology_one_res_rootsOfUnityModule K Ksep hn V
  · exact finite_cohomology_two_res_rootsOfUnityModule K Ksep hn V

end Kummer

end Local

section Fixing

/-- For `c ≠ 0` with `p • c = 0` (`p` prime), the map `ℤ/p → X`, `1 ↦ c`, is injective. -/
theorem zmod_lift_zmultiplesHom_injective {X : Type*} [AddCommGroup X] {p : ℕ} [Fact p.Prime]
    {c : X} (hc : c ≠ 0) (hpc : p • c = 0) :
    Function.Injective (ZMod.lift p ⟨zmultiplesHom X c, by simp [hpc]⟩) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hord : addOrderOf c = p := addOrderOf_eq_prime hpc hc
  rw [← ZMod.intCast_zmod_cast x, ZMod.lift_coe, zmultiplesHom_apply] at hx
  have h := (addOrderOf_dvd_iff_zsmul_eq_zero).2 hx
  rw [hord] at h
  rw [← ZMod.intCast_zmod_cast x]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h

section RootsOfUnity

variable (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsIntegral F E] (n : ℕ)
  [NeZero n]

/-- The open subgroup of `Gal(E/F)` fixing the `n`-th roots of unity of `E`. -/
def rootsOfUnityFixing : OpenSubgroup Gal(E/F) where
  toSubgroup := ⨅ x : rootsOfUnityModule F E n, vectorStabilizer (rootsOfUnityModule F E n).ρ x
  isOpen' := by
    have : Finite (rootsOfUnityModule F E n) :=
      inferInstanceAs (Finite (Additive (rootsOfUnity n E)))
    change IsOpen (((⨅ x : rootsOfUnityModule F E n,
      vectorStabilizer (rootsOfUnityModule F E n).ρ x : Subgroup Gal(E/F))) : Set Gal(E/F))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun x => IsSmoothRep.isOpen_stabilizer _ x

variable {F E n} in
theorem apply_eq_of_mem_rootsOfUnityFixing {σ : Gal(E/F)} (hσ : σ ∈ rootsOfUnityFixing F E n)
    {ζ : E} (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hu : IsUnit ζ := IsUnit.of_pow_eq_one hζ (NeZero.ne n)
  let x : rootsOfUnityModule F E n :=
    Additive.ofMul ⟨hu.unit, (mem_rootsOfUnity n _).2 (Units.ext (by simpa using hζ))⟩
  have h := Subgroup.mem_iInf.1 hσ x
  exact congrArg (fun y : Additive (rootsOfUnity n E) =>
    (((Additive.toMul y : rootsOfUnity n E) : Eˣ) : E)) h

end RootsOfUnity

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] (n : ℕ)
  [NeZero n]

omit [IsSepClosure K Ksep] [NeZero n] in
/-- For `p` invertible in `K`, a separable closure of `K` has exactly `p` roots of unity of
order dividing `p`. -/
theorem natCard_rootsOfUnity_of_ne_zero [IsSepClosure K Ksep] {p : ℕ} (hp : (p : K) ≠ 0) :
    Nat.card (rootsOfUnity p Ksep) = p := by
  have : NeZero (p : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero_iff _ (algebraMap K Ksep).injective).2 hp⟩
  have : NeZero p := .of_neZero_natCast Ksep
  have : IsSepClosed Ksep := ‹IsSepClosure K Ksep›.sep_closed
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ksep p

end Fixing

namespace Local

section Trivial

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ksep : Type u) [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ} (hn : (n : K) ≠ 0)

include hn in
/-- Finiteness in degrees `≤ 2` for finite `n`-torsion modules with trivial action of an open
subgroup `V` that fixes the `n`-th roots of unity: by induction on the order, through a
submodule `ℤ/p ≅ μ_p`. -/
theorem finite_cohomology_of_trivial (V : OpenSubgroup Gal(Ksep/K))
    (hV : ∀ σ ∈ V, ∀ ζ : Ksep, ζ ^ n = 1 → σ ζ = ζ) :
    ∀ (A : Rep.{u} (ULift.{u} ℤ) (V : Subgroup Gal(Ksep/K))) [IsSmoothRep A] [Finite A],
      (∀ (g : (V : Subgroup Gal(Ksep/K))) (a : A), A.ρ g a = a) → (∀ a : A, n • a = 0) →
      ∀ r ≤ 2, Finite (cohomology A r) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  intro A
  induction hN : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ N ih =>
  intro _ _ htriv hA r hr
  by_cases hsub : Subsingleton A
  · have := subsingleton_cohomology_of_subsingleton A r
    exact Finite.of_subsingleton
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 0 := by
    rw [not_subsingleton_iff_nontrivial] at hsub
    exact exists_ne 0
  have hdn : addOrderOf a ∣ n := addOrderOf_dvd_of_nsmul_eq_zero (hA a)
  have hd0 : addOrderOf a ≠ 0 := fun h0 => hn0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdn))
  have hd1 : addOrderOf a ≠ 1 := fun h1 =>
    ha (by rw [← one_nsmul a, ← h1, addOrderOf_nsmul_eq_zero])
  set d := addOrderOf a with hd
  set p := d.minFac
  have hp : p.Prime := Nat.minFac_prime hd1
  have : Fact p.Prime := ⟨hp⟩
  have hpd : p ∣ d := Nat.minFac_dvd d
  set b := (d / p) • a
  have hpb : p • b = 0 := by
    rw [smul_smul, Nat.mul_div_cancel' hpd, hd, addOrderOf_nsmul_eq_zero]
  have hb : b ≠ 0 := by
    intro hb0
    have h1 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hpd) hp.pos)
      (addOrderOf_dvd_of_nsmul_eq_zero hb0)
    exact absurd h1 (not_le.2 (Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hp.one_lt))
  have hpn : p ∣ n := hpd.trans hdn
  have hpK : (p : K) ≠ 0 := fun h0 => hn (by
    obtain ⟨c, hc⟩ := hpn
    rw [hc, Nat.cast_mul, h0, zero_mul])
  have hcard := natCard_rootsOfUnity_of_ne_zero K Ksep hpK
  have : Finite (rootsOfUnity p Ksep) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Nontrivial (rootsOfUnity p Ksep) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hp.one_lt)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : rootsOfUnity p Ksep)
  have hζ0 : Additive.ofMul ζ ≠ 0 := hζ
  have hζp : p • Additive.ofMul ζ = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity p Ksep) (x := ζ)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  let j : ZMod p →+ Additive (rootsOfUnity p Ksep) :=
    ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul ζ), by simp [hζp]⟩
  have hj : Function.Bijective j :=
    (zmod_lift_zmultiplesHom_injective hζ0 hζp).bijective_of_nat_card_le (by
      rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard])
  let e : ZMod p ≃+ Additive (rootsOfUnity p Ksep) := AddEquiv.ofBijective j hj
  let i : ZMod p →+ A := ZMod.lift p ⟨zmultiplesHom A b, by simp [hpb]⟩
  have hi : Function.Injective i := zmod_lift_zmultiplesHom_injective hb hpb
  have hfix : ∀ (σ : (V : Subgroup Gal(Ksep/K))) (x : Additive (rootsOfUnity p Ksep)),
      (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep p)).ρ σ x = x := by
    intro σ x
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    refine hV σ σ.2 _ ?_
    obtain ⟨c, hc⟩ := hpn
    have hxp : (((Additive.toMul x : rootsOfUnity p Ksep) : Ksepˣ) : Ksep) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity p _).1 (Additive.toMul x).2, Units.val_one]
    rw [hc, pow_mul, hxp, one_pow]
  let ι : Rep.res (V : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep p) ⟶ A :=
    Rep.ofHom ⟨(uliftIntLinearEquivAddHom (Rep.res (V : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep p)) A).symm (i.comp e.symm.toAddMonoidHom),
      fun σ => LinearMap.ext fun x => by
        change i (e.symm ((Rep.res (V : Subgroup Gal(Ksep/K)).subtype
          (rootsOfUnityModule K Ksep p)).ρ σ x)) = A.ρ σ (i (e.symm x))
        rw [hfix, htriv]⟩
  have hι : Function.Injective ι.hom := fun x y h => e.symm.injective (hi h)
  let S := cokerShortComplex ι
  have hS : S.ShortExact := cokerShortComplex_shortExact ι hι
  have : IsSmoothRep S.X₁ := inferInstanceAs
    (IsSmoothRep (Rep.res (V : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep p)))
  have : IsSmoothRep S.X₂ := (inferInstance : IsSmoothRep A)
  have : Finite S.X₂ := (inferInstance : Finite A)
  have : IsSmoothRep S.X₃ := isSmoothRep_quotient _ _ _
  have hsurj : Function.Surjective S.g.hom := Submodule.mkQ_surjective _
  have : Finite S.X₃ := Finite.of_surjective _ hsurj
  have htrivQ : ∀ (g : (V : Subgroup Gal(Ksep/K))) (q : S.X₃), S.X₃.ρ g q = q := by
    intro g q
    obtain ⟨a', rfl⟩ := hsurj q
    exact (Rep.hom_comm_apply S.g g a').symm.trans (congrArg S.g.hom (htriv g a'))
  have hQ : ∀ q : S.X₃, n • q = 0 := by
    intro q
    obtain ⟨a', rfl⟩ := hsurj q
    rw [← map_nsmul]
    exact (congrArg S.g.hom (hA a')).trans (map_zero _)
  have hlt : Nat.card S.X₃ < N := by
    rw [← hN]
    have := Fintype.ofFinite S.X₃
    have := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_surjective_not_injective _ hsurj fun hinj => hb ?_
    have h0 : S.g.hom (ι.hom (e 1)) = 0 :=
      congrArg (fun φ => φ.hom (e 1)) S.zero
    have h1 : ι.hom (e 1) = b := by
      change i (e.symm (e 1)) = b
      rw [AddEquiv.symm_apply_apply,
        show (1 : ZMod p) = ((1 : ℤ) : ZMod p) from Int.cast_one.symm, ZMod.lift_coe]
      exact one_zsmul b
    rw [← h1]
    exact hinj (h0.trans (map_zero _).symm)
  have h3 : Finite (cohomology S.X₃ r) := ih _ hlt S.X₃ rfl htrivQ hQ r hr
  have h1 : Finite (cohomology S.X₁ r) := finite_cohomology_res_rootsOfUnityModule K Ksep hpK V r hr
  exact finite_of_exact (coeffMap S.f r).hom.toAddMonoidHom (coeffMap S.g r).hom.toAddMonoidHom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (cohomology_exact₂ hS r))

include hn in
/-- For an open subgroup `U` and a finite smooth module `M` of `U` killed by `n` invertible in
`K`, `Hʳ(U, M)` is finite for `r ≤ 2`. -/
theorem finite_cohomology_res_of_le_two (U : OpenSubgroup Gal(Ksep/K))
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup Gal(Ksep/K))) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) (r : ℕ) (hr : r ≤ 2) : Finite (cohomology M r) := by
  have hn0 : n ≠ 0 := fun h0 => hn (by simp [h0])
  have : NeZero n := ⟨hn0⟩
  exact finite_cohomology_of_forall_trivial n 2 (rootsOfUnityFixing K Ksep n)
    (fun V hV A _ _ htriv hA r hr => finite_cohomology_of_trivial K Ksep hn V
      (fun σ hσ ζ hζ => apply_eq_of_mem_rootsOfUnityFixing (hV hσ) hζ) A htriv hA r hr)
    U M hM r hr

end Trivial

end Local

end Langlands.GaloisCohomology
