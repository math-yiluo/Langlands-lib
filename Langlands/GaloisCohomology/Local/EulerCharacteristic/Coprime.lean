import Langlands.GaloisCohomology.Local.EulerCharacteristic.Units
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Twist
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Kummer
import Langlands.GaloisCohomology.Local.Arithmetic.SeparableClosure
import Langlands.GaloisCohomology.Local.Finiteness
import Mathlib.Algebra.Field.ULift

/-!
# The Euler characteristic when the module is trivial on a subgroup of index prime to `l`

Let `V ≤ U` be open subgroups of `Gal(Ksep/K)`, `V` normal in `U` of index prime to `l`, with `μ_l`
contained in the fixed field `F` of `V`, and let `M` be a finite `l`-torsion module of `U` on which
`V` acts trivially. Then `χ(U, M) = |M|^{-n}` where `|𝒪[E]/l| = lⁿ`, `E` the fixed field of `U`.
The cohomology of `U` is computed as the `Gal(F/E)`-invariants of the cohomology of `V`
(twisted by `Hom(μ_l, M)`, `Twist.lean`); in degree one Kummer theory identifies `H¹(V, μ_l)` with
`Fˣ/Fˣˡ`, whose value under an additive function is computed in `Units.lean`.

The valuative relation and topology of `Ksep` are hypotheses (`[ValuativeRel Ksep]`,
`[TopologicalSpace Ksep]`, `[IsValuativeTopology Ksep]`, `[ValuativeExtension K Ksep]`); fixed fields
are local fields through the scoped instances of `Arithmetic/SeparableClosure.lean`.
-/

noncomputable section

open Langlands.GaloisCohomology.Local.IntermediateFieldStructure

namespace Langlands.GaloisCohomology.Local

universe u

-- from Coprime.lean
open CategoryTheory IntermediateField Representation ValuativeRel Langlands.ProfiniteCohomology

section Card

variable (l : ℕ) [Fact l.Prime]

theorem natCard_eq_pow_finrank_zmod (V : Type*) [AddCommGroup V] [Module (ULift.{u} (ZMod l)) V]
    [Finite V] : Nat.card V = l ^ Module.finrank (ULift.{u} (ZMod l)) V := by
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ULift.{u} (ZMod l)) (V := V),
    Fintype.card_ulift, ZMod.card]

theorem finrank_eq_of_natCard_zmod {V : Type*} [AddCommGroup V] [Module (ULift.{u} (ZMod l)) V]
    [Finite V] {r : ℕ} (h : Nat.card V = l ^ r) : Module.finrank (ULift.{u} (ZMod l)) V = r := by
  rw [natCard_eq_pow_finrank_zmod l V] at h
  exact Nat.pow_right_injective (Fact.out : l.Prime).two_le h

end Card

section Roots

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] (l : ℕ)

theorem nsmul_galRootsOfUnity_eq_zero (a : rootsOfUnityModule K Ksep l) : l • a = 0 := by
  have key : ∀ b : Additive (rootsOfUnity l Ksep), l • b = 0 := fun b => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using (mem_rootsOfUnity l _).1 (Additive.toMul b).2)
  exact key a

noncomputable abbrev rootsRepZMod (U : Subgroup Gal(Ksep/K)) : Rep.{u} (ULift.{u} (ZMod l)) U :=
  zmodRepOfTorsion l (Rep.res U.subtype (rootsOfUnityModule K Ksep l))
    (nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := Ksep) l)

variable [IsSepClosure K Ksep]

theorem finrank_rootsRepZMod [Fact l.Prime] (hl : (l : K) ≠ 0) (U : Subgroup Gal(Ksep/K)) :
    Module.finrank (ULift.{u} (ZMod l)) (rootsRepZMod (K := K) (Ksep := Ksep) l U) = 1 := by
  have hlp : l.Prime := Fact.out
  have : IsSepClosed Ksep := IsSepClosure.sep_closed K
  have : NeZero (l : Ksep) := ⟨by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero _).mpr hl⟩
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hcard : Nat.card (rootsRepZMod (K := K) (Ksep := Ksep) l U) = l ^ 1 :=
    (Nat.card_congr (Additive.toMul (α := rootsOfUnity l Ksep))).trans
      ((HasEnoughRootsOfUnity.natCard_rootsOfUnity Ksep l).trans (pow_one l).symm)
  have : Finite (rootsRepZMod (K := K) (Ksep := Ksep) l U) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ hlp.ne_zero)
  exact finrank_eq_of_natCard_zmod l hcard

end Roots

section RootsSubgroupOf

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {l : ℕ}
  {U V : OpenSubgroup Gal(Ksep/K)}

omit [IsSepClosure K Ksep] in

theorem rootsRepZMod_ρ_of_mem
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))))
    (t : rootsRepZMod (K := K) (Ksep := Ksep) l U) :
    (rootsRepZMod (K := K) (Ksep := Ksep) l U).ρ g t = t := by
  have hg : (((g : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K))) ∈ (V : Subgroup Gal(Ksep/K)) :=
    Subgroup.mem_subgroupOf.1 g.2
  have key : ∀ s : Additive (rootsOfUnity l Ksep),
      (rootsOfUnityModule K Ksep l).ρ ((g : (U : Subgroup Gal(Ksep/K))) : Gal(Ksep/K)) s = s := by
    intro s
    rw [rootsOfUnityModule_ρ_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    rw [toMul_ofMul, coe_galRootsOfUnityHom_apply]
    have hs : (((Additive.toMul s : rootsOfUnity l Ksep) : Ksepˣ) : Ksep) ^ l = 1 := by
      have := (mem_rootsOfUnity l _).1 (Additive.toMul s).2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    exact (mem_fixedField_iff _ _).1 (hμ _ hs) _ hg
  exact key t

variable (l) in

noncomputable def rootsCohomologyZModEquiv (n : ℕ) :
    cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep l))) n ≃+
      cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (rootsRepZMod (K := K) (Ksep := Ksep) l U)) n :=
  cohomologyAddEquivOfEquiv
    (A := Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
      (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep l)))
    (A' := Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
      (rootsRepZMod (K := K) (Ksep := Ksep) l U))
    (zmodRepOfTorsionEquiv l _ (nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := Ksep) l))
    (fun _ _ => rfl) n

theorem rootsCohomologyZModEquiv_cohomologyConj
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal] (n : ℕ)
    (g : (U : Subgroup Gal(Ksep/K)))
    (x : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep l))) n) :
    rootsCohomologyZModEquiv l n ((cohomologyConj (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (rootsOfUnityModule K Ksep l)) ((V : Subgroup Gal(Ksep/K)).subgroupOf
          (U : Subgroup Gal(Ksep/K))) n g).hom x) =
      (cohomologyConj (rootsRepZMod (K := K) (Ksep := Ksep) l U) ((V : Subgroup Gal(Ksep/K)).subgroupOf
          (U : Subgroup Gal(Ksep/K))) n g).hom (rootsCohomologyZModEquiv l n x) :=
  cohomologyAddEquivOfEquiv_cohomologyConj (A := Rep.res (U : Subgroup Gal(Ksep/K)).subtype
    (rootsOfUnityModule K Ksep l)) (A' := rootsRepZMod (K := K) (Ksep := Ksep) l U)
    (zmodRepOfTorsionEquiv l _ (nsmul_galRootsOfUnity_eq_zero (K := K) (Ksep := Ksep) l))
    (fun _ _ => rfl) _ n g x

end RootsSubgroupOf

section Local

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {l : ℕ} {U V : OpenSubgroup Gal(Ksep/K)}

theorem finite_cohomology_roots_subgroupOf (hl : (l : K) ≠ 0) (h : V ≤ U)
    (n : ℕ) (hn : n ≤ 2) :
    Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).subtype
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep l))) n) := by
  have := finite_cohomology_res_rootsOfUnityModule K Ksep hl V n hn
  exact Finite.of_equiv _ (asIso (map (subgroupOfEquivOfLeSymmHom
      (show (V : Subgroup Gal(Ksep/K)) ≤ U from h)) (resSubgroupOfHom _ (rootsOfUnityModule K Ksep l))
      n)).toLinearEquiv.toEquiv.symm

end Local

section ZModLinear

variable {l : ℕ} {X Y : Type*} [AddCommGroup X] [Module (ULift.{u} (ZMod l)) X] [AddCommGroup Y]
  [Module (ULift.{u} (ZMod l)) Y]

/-- `ULift (ZMod l)` acts through the integers: `c • x = c̃ • x` for an integer `c̃` lifting `c`. -/
theorem ulift_zmod_smul_eq_zsmul (c : ULift.{u} (ZMod l)) (x : X) :
    c • x = (c.down.cast : ℤ) • x := by
  have hc : ((c.down.cast : ℤ) : ULift.{u} (ZMod l)) = c :=
    ULift.ext (ZMod.intCast_zmod_cast c.down)
  conv_lhs => rw [← hc]
  exact Int.cast_smul_eq_zsmul _ _ _

/-- An additive isomorphism of modules over `ULift (ZMod l)` is linear. -/
noncomputable def addEquivZModLinear (φ : X ≃+ Y) : X ≃ₗ[ULift.{u} (ZMod l)] Y :=
  { φ.toAddMonoidHom with
    map_smul' := fun c x => by
      change φ (c • x) = c • φ x
      rw [ulift_zmod_smul_eq_zsmul, ulift_zmod_smul_eq_zsmul, map_zsmul]
    invFun := φ.symm
    left_inv := φ.symm_apply_apply
    right_inv := φ.apply_symm_apply }

theorem addEquivZModLinear_apply (φ : X ≃+ Y) (x : X) : addEquivZModLinear (l := l) φ x = φ x :=
  rfl

end ZModLinear

section ULiftRep

variable {l : ℕ} {Γ X : Type*} [Group Γ] [AddCommGroup X] [Module (ZMod l) X]

/-- A representation over `ZMod l` as a representation over `ULift (ZMod l)`, which acts through
`ZMod l` (`ULift.module`). -/
def zmodRepULift (ρ : Representation (ZMod l) Γ X) : Representation (ULift.{u} (ZMod l)) Γ X where
  toFun γ :=
    { toFun := ρ γ
      map_add' := map_add (ρ γ)
      map_smul' := fun c x => (ρ γ).map_smul c.down x }
  map_one' := by
    ext x
    change ρ 1 x = x
    rw [map_one, Module.End.one_apply]
  map_mul' γ δ := by
    ext x
    change ρ (γ * δ) x = ρ γ (ρ δ x)
    rw [map_mul, Module.End.mul_apply]

theorem zmodRepULift_apply (ρ : Representation (ZMod l) Γ X) (γ : Γ) (x : X) :
    zmodRepULift.{u} ρ γ x = ρ γ x :=
  rfl

end ULiftRep

section Invariants

/-- The dimension of the invariants of `X ⊗ N` depends on the representation `X` only up to
equivariant isomorphism. -/
theorem finrank_invariants_tprod_eq_of_linearEquiv {k Γ X Y N : Type*} [Field k] [Group Γ]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] [AddCommGroup N] [Module k N]
    (ρ₁ : Representation k Γ X) (ρ₂ : Representation k Γ Y) (σ : Representation k Γ N)
    (e : X ≃ₗ[k] Y) (he : ∀ γ x, e (ρ₁ γ x) = ρ₂ γ (e x)) :
    Module.finrank k (ρ₁.tprod σ).invariants = Module.finrank k (ρ₂.tprod σ).invariants := by
  have h₁ : (ρ₁.tprod σ).IsIntertwiningMap (ρ₂.tprod σ) (e.toLinearMap.rTensor N) :=
    isIntertwiningMap_rTensor σ ⟨he⟩
  have h₂ : (ρ₂.tprod σ).IsIntertwiningMap (ρ₁.tprod σ) (e.symm.toLinearMap.rTensor N) :=
    isIntertwiningMap_rTensor σ ⟨fun γ y => by
      apply e.injective
      change e (e.symm (ρ₂ γ y)) = e (ρ₁ γ (e.symm y))
      rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]⟩
  let E := e.rTensor N
  have hmap : (ρ₂.tprod σ).invariants = (ρ₁.tprod σ).invariants.map E.toLinearMap := by
    ext y
    constructor
    · intro hy
      refine ⟨E.symm y, mapsTo_invariants h₂ y hy, E.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact mapsTo_invariants h₁ x hx
  rw [hmap, LinearEquiv.finrank_map_eq]

/-- For the regular representation of a finite group `Γ` over `ZMod l`, viewed over
`ULift (ZMod l)`: `dim (k[Γ] ⊗ N)^Γ = dim N`. -/
theorem finrank_invariants_zmodRepULift_leftRegular_tprod {l : ℕ} [Fact l.Prime] {Γ N : Type*}
    [Group Γ] [Fintype Γ] [DecidableEq Γ] [AddCommGroup N] [Module (ULift.{u} (ZMod l)) N]
    (σ : Representation (ULift.{u} (ZMod l)) Γ N) :
    Module.finrank (ULift.{u} (ZMod l)) ((zmodRepULift.{u} (leftRegular (ZMod l) Γ)).tprod σ).invariants =
      Module.finrank (ULift.{u} (ZMod l)) N := by
  let E : MonoidAlgebra (ZMod l) Γ ≃+ MonoidAlgebra (ULift.{u} (ZMod l)) Γ :=
    (MonoidAlgebra.coeffAddEquiv.trans (Finsupp.mapRange.addEquiv AddEquiv.ulift.symm)).trans
      MonoidAlgebra.coeffAddEquiv.symm
  have hE : ∀ m r, E (MonoidAlgebra.single m r) = MonoidAlgebra.single m (ULift.up r) :=
    fun m r => by simp [E, Finsupp.mapRange_single]; rfl
  have key := finrank_invariants_tprod_eq_of_linearEquiv (zmodRepULift.{u} (leftRegular (ZMod l) Γ))
    (leftRegular (ULift.{u} (ZMod l)) Γ) σ (addEquivZModLinear E) ?_
  · exact key.trans (finrank_invariants_leftRegular_tprod σ)
  intro γ x
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r =>
    rw [addEquivZModLinear_apply, addEquivZModLinear_apply, zmodRepULift_apply,
      ofMulAction_single, hE, hE, ofMulAction_single]

end Invariants

namespace AdditiveFunction

open TensorProduct

/-- For a representation `σ` over `ULift (ZMod l)` of a finite group `Γ` of order prime to `l` on a
finite-dimensional space `N`, the additive function `X ↦ dim (X ⊗ N)^Γ` (dimensions over
`ULift (ZMod l)`; `X` is viewed over `ULift (ZMod l)` by `zmodRepULift`). -/
noncomputable def invariantsTensorULift (l : ℕ) [Fact l.Prime] (Γ : Type*) [Group Γ] [Finite Γ]
    (hΓ : Nat.Coprime (Nat.card Γ) l) {N : Type*} [AddCommGroup N]
    [Module (ULift.{u} (ZMod l)) N] [Module.Finite (ULift.{u} (ZMod l)) N]
    (σ : Representation (ULift.{u} (ZMod l)) Γ N) : AdditiveFunction.{u} l Γ where
  toFun X _ _ _ ρ := Module.finrank (ULift.{u} (ZMod l)) ((zmodRepULift.{u} ρ).tprod σ).invariants
  additive := by
    intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ f g hf hg hinj hfg hs
    have := Fintype.ofFinite Γ
    have hΓ' : (Fintype.card Γ : ULift.{u} (ZMod l)) ≠ 0 := by
      intro h0
      have h0' : (Fintype.card Γ : ZMod l) = 0 := congrArg ULift.down h0
      rw [← Nat.card_eq_fintype_card, ZMod.natCast_eq_zero_iff] at h0'
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hΓ.symm h0'
    let f' : X₁ →ₗ[ULift.{u} (ZMod l)] X₂ :=
      { toFun := f, map_add' := map_add f, map_smul' := fun c x => f.map_smul c.down x }
    let g' : X₂ →ₗ[ULift.{u} (ZMod l)] X₃ :=
      { toFun := g, map_add' := map_add g, map_smul' := fun c x => g.map_smul c.down x }
    have hf' : (zmodRepULift.{u} ρ₁).IsIntertwiningMap (zmodRepULift.{u} ρ₂) f' :=
      ⟨fun γ x => hf.isIntertwining γ x⟩
    have hg' : (zmodRepULift.{u} ρ₂).IsIntertwiningMap (zmodRepULift.{u} ρ₃) g' :=
      ⟨fun γ x => hg.isIntertwining γ x⟩
    have := Module.Finite.of_finite (R := ULift.{u} (ZMod l)) (M := X₂)
    have : Module.Free (ULift.{u} (ZMod l)) N := Module.Free.of_divisionRing (ULift.{u} (ZMod l)) N
    have : Module.Flat (ULift.{u} (ZMod l)) N := Module.Flat.of_free
    have hinj' : Function.Injective (f'.rTensor N) :=
      Module.Flat.rTensor_preserves_injective_linearMap f' hinj
    have hex : Function.Exact (f'.rTensor N) (g'.rTensor N) := rTensor_exact N hfg hs
    have hs' : Function.Surjective (g'.rTensor N) := LinearMap.rTensor_surjective N hs
    have key := finrank_invariants_additive hΓ' (f'.rTensor N) (g'.rTensor N)
      (isIntertwiningMap_rTensor σ hf') (isIntertwiningMap_rTensor σ hg') hinj' hex hs'
    exact_mod_cast key

theorem invariantsTensorULift_apply (l : ℕ) [Fact l.Prime] (Γ : Type*) [Group Γ] [Finite Γ]
    (hΓ : Nat.Coprime (Nat.card Γ) l) {N : Type*} [AddCommGroup N]
    [Module (ULift.{u} (ZMod l)) N] [Module.Finite (ULift.{u} (ZMod l)) N]
    (σ : Representation (ULift.{u} (ZMod l)) Γ N) (X : Type u) [AddCommGroup X]
    [Module (ZMod l) X] [Finite X] (ρ : Representation (ZMod l) Γ X) :
    (invariantsTensorULift l Γ hΓ σ).toFun X ρ =
      Module.finrank (ULift.{u} (ZMod l)) ((zmodRepULift.{u} ρ).tprod σ).invariants :=
  rfl

end AdditiveFunction

section Assembly

variable {K Ksep : Type u} [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {l : ℕ} [Fact l.Prime] {U V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ U)
  [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

include h in

theorem toFun_cohomologyConjRep_eq {N : Type*} [AddCommGroup N] [Module (ULift.{u} (ZMod l)) N]
    (σ : letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
      Representation (ULift.{u} (ZMod l)) (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
        (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))) N)
    (i : ℕ) {Y : Type u} [AddCommGroup Y] [Module (ZMod l) Y]
    (ρY : letI := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
      Representation (ZMod l) (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
        (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))) Y)
    (φ : cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
        (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i ≃+ Y)
    (hφ : ∀ (g : (U : Subgroup Gal(Ksep/K))) x,
      φ ((cohomologyConj (rootsRepZMod (K := K) (Ksep := Ksep) l U) ((V : Subgroup Gal(Ksep/K)).subgroupOf
        (U : Subgroup Gal(Ksep/K))) i g).hom x) = ρY (fixedFieldGalHom h g) (φ x)) :
    haveI : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
      compactSpace_openSubgroup (openSubgroupOf U V)
    Module.finrank (ULift.{u} (ZMod l)) (Representation.tprod
        ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).comp
        (quotientFixedFieldGalEquiv h).symm.toMonoidHom) σ).invariants =
      Module.finrank (ULift.{u} (ZMod l)) ((zmodRepULift.{u} ρY).tprod σ).invariants := by
  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
    compactSpace_openSubgroup (openSubgroupOf U V)
  refine finrank_invariants_tprod_eq_of_linearEquiv _ _ σ (addEquivZModLinear φ) fun γ x => ?_
  obtain ⟨q, rfl⟩ := (quotientFixedFieldGalEquiv h).surjective γ
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [addEquivZModLinear_apply, addEquivZModLinear_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, cohomologyConjRep_mk, hφ,
      quotientFixedFieldGalEquiv_mk]
    rfl

end Assembly

section Main

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  [ValuativeRel Ksep] [TopologicalSpace Ksep] [IsValuativeTopology Ksep] [ValuativeExtension K Ksep]
  {l : ℕ} [Fact l.Prime] {U V : OpenSubgroup Gal(Ksep/K)}

-- The elaboration of this proof (the cohomology of `U` as twisted invariants of the cohomology
-- of `V`, assembled in degrees 0, 1, 2) exceeds the default limit; raised as in the source.
set_option maxHeartbeats 400000 in

theorem finrank_cohomology_alternating_sum_coprime (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{u} (ULift.{u} (ZMod l)) (U : Subgroup Gal(Ksep/K))) [IsSmoothRep M]
    [Module.Finite (ULift.{u} (ZMod l)) M]
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    {n : ℕ} (hn : Nat.card (𝒪[fixedField (U : Subgroup Gal(Ksep/K))] ⧸
      Ideal.span {(l : 𝒪[fixedField (U : Subgroup Gal(Ksep/K))])}) = l ^ n) :
    (Module.finrank (ULift.{u} (ZMod l)) (cohomology M 0) : ℤ) -
        Module.finrank (ULift.{u} (ZMod l)) (cohomology M 1) +
      Module.finrank (ULift.{u} (ZMod l)) (cohomology M 2) =
        -(n * Module.finrank (ULift.{u} (ZMod l)) M) := by
  classical
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩

  have : CompactSpace (U : Subgroup Gal(Ksep/K)) := compactSpace_openSubgroup U
  have : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
    compactSpace_openSubgroup (openSubgroupOf U V)
  have hT : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))))
      (t : rootsRepZMod (K := K) (Ksep := Ksep) l U),
      (rootsRepZMod (K := K) (Ksep := Ksep) l U).ρ g t = t :=
    rootsRepZMod_ρ_of_mem hμ
  have hM' : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K)))) (m : M),
      M.ρ g m = m :=
    fun g m => hM g (Subgroup.mem_subgroupOf.1 g.2) m
  have hTr : Module.finrank (ULift.{u} (ZMod l)) (rootsRepZMod (K := K) (Ksep := Ksep) l U) = 1 :=
    finrank_rootsRepZMod l hl _
  have hrel0 : (V : Subgroup Gal(Ksep/K)).relIndex U ≠ 0 := fun h0 => by
    rw [h0, Nat.coprime_zero_left] at hcop
    exact hlp.one_lt.ne' hcop
  have hP : (((openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))).index :
      ULift.{u} (ZMod l))) ≠ 0 := fun h0 => by
    have h0' : (((V : Subgroup Gal(Ksep/K)).relIndex U : ℕ) : ZMod l) = 0 := congrArg ULift.down h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hcop.symm h0'
  have hkey := finrank_cohomology_eq_finrank_invariants (openSubgroupOf U V)
    (rootsRepZMod (K := K) (Ksep := Ksep) l U) M hT hM' hTr hP

  let := (IntermediateField.inclusion (fixedField_le_fixedField h)).toRingHom.toAlgebra
  have hcardΓ : Nat.card (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))) =
      (V : Subgroup Gal(Ksep/K)).relIndex U :=
    (Nat.card_congr (quotientFixedFieldGalEquiv h).toEquiv).symm
  have : Finite (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
      fixedField (V : Subgroup Gal(Ksep/K))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardΓ]; exact hrel0)
  have hΓ : Nat.Coprime (Nat.card (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K)))) l := by
    rw [hcardΓ]; exact hcop
  have : Module.Finite (ULift.{u} (ZMod l)) (rootsRepZMod (K := K) (Ksep := Ksep) l U) :=
    Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite (ULift.{u} (ZMod l)) (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M) :=
    inferInstanceAs (Module.Finite (ULift.{u} (ZMod l))
      (rootsRepZMod (K := K) (Ksep := Ksep) l U →ₗ[ULift.{u} (ZMod l)] M))
  let σ := quotientRep (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K)))
    (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M) (homRep_ρ_of_mem _ _ _ hT hM')
  let d : AdditiveFunction.{u} l (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))) :=
    AdditiveFunction.invariantsTensorULift l _ hΓ (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom)

  have hstep : ∀ i : ℕ, (Module.finrank (ULift.{u} (ZMod l)) (cohomology M i) : ℤ) =
      Module.finrank (ULift.{u} (ZMod l)) (Representation.tprod
        ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).comp
          (quotientFixedFieldGalEquiv h).symm.toMonoidHom)
        (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom)).invariants := by
    intro i
    rw [hkey i]
    have hc : Representation.tprod ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
        ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).comp
          (quotientFixedFieldGalEquiv h).symm.toMonoidHom)
        (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom) =
        ((cohomologyConjRep (rootsRepZMod (K := K) (Ksep := Ksep) l U)
          ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) i).tprod σ).comp
          (quotientFixedFieldGalEquiv h).symm.toMonoidHom := rfl
    rw [hc, invariants_comp_of_surjective _ _ (quotientFixedFieldGalEquiv h).symm.surjective]

  have hX : ∀ i ≤ 2, Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
      (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i) :=
    fun i hi => by
      have := finite_cohomology_roots_subgroupOf (K := K) (Ksep := Ksep) hl h i hi
      exact Finite.of_equiv _ (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
        l i).toEquiv
  have hX0 := hX 0 (by norm_num)
  have hX1 := hX 1 (by norm_num)
  have hX2 := hX 2 (by norm_num)

  let φ0 := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V) l 0).symm.trans
    (cohomologyZeroRootsEquiv h l)
  have : Finite (TorsN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l) :=
    Finite.of_equiv _ φ0.toEquiv
  have e0 := toFun_cohomologyConjRep_eq h (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom) 0 _ φ0 (fun g x => by
    obtain ⟨y, rfl⟩ := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l 0).surjective x
    simp only [φ0, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← rootsCohomologyZModEquiv_cohomologyConj, AddEquiv.symm_apply_apply]
    exact cohomologyZeroRootsEquiv_cohomologyConj_gal h l g y)

  let φ1 := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V) l 1).symm.trans
    (cohomologyOneRootsEquiv h hl)
  have : Finite (ModN (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l) :=
    Finite.of_equiv _ φ1.toEquiv
  have e1 := toFun_cohomologyConjRep_eq h (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom) 1 _ φ1 (fun g x => by
    obtain ⟨y, rfl⟩ := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l 1).surjective x
    simp only [φ1, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← rootsCohomologyZModEquiv_cohomologyConj, AddEquiv.symm_apply_apply]
    exact cohomologyOneRootsEquiv_cohomologyConj_gal h hl g y)

  let φ2 := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V) l 2).symm.trans
    ((cohomologyTwoRootsEquiv hl h).trans (AddEquiv.ulift.{0, u} (α := ZMod l)).symm)
  have : Finite (ULift.{u} (ZMod l)) := Finite.of_equiv (ZMod l) Equiv.ulift.symm
  -- the additive group and the `ZMod l`-module structure of `ULift (ZMod l)` used by
  -- `AdditiveFunction.one` (not those coming from the field `ULift (ZMod l)`)
  let : AddCommGroup (ULift.{u} (ZMod l)) := ULift.addCommGroup
  let : Module (ZMod l) (ULift.{u} (ZMod l)) := ULift.module'
  have e2 := toFun_cohomologyConjRep_eq h (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom) 2
    (Representation.trivial (ZMod l) _ (ULift.{u} (ZMod l))) φ2 (fun g x => by
    obtain ⟨y, rfl⟩ := (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l 2).surjective x
    simp only [φ2, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rw [← rootsCohomologyZModEquiv_cohomologyConj, AddEquiv.symm_apply_apply,
      cohomologyTwoRootsEquiv_cohomologyConj]
    rfl)

  have : IsScalarTower K (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) := Module.Finite.of_restrictScalars_finite K _ _
  have : ValuativeExtension (fixedField (U : Subgroup Gal(Ksep/K)))
      (fixedField (V : Subgroup Gal(Ksep/K))) :=
    valuativeExtension_inclusion (fixedField_le_fixedField h)
  have : IsGalois (fixedField (U : Subgroup Gal(Ksep/K))) (fixedField (V : Subgroup Gal(Ksep/K))) :=
    IsGalois.of_card_aut_eq_finrank (F := fixedField (U : Subgroup Gal(Ksep/K)))
      (E := fixedField (V : Subgroup Gal(Ksep/K))) (by rw [hcardΓ, relIndex_eq_finrank h])
  have hlE : (l : fixedField (U : Subgroup Gal(Ksep/K))) ≠ 0 := by
    rw [← map_natCast (algebraMap K (fixedField (U : Subgroup Gal(Ksep/K))))]
    exact (map_ne_zero _).mpr hl
  have hg := g_units_eq d hlE hn
  rw [d.g_eq] at hg
  have : Fintype (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField (U : Subgroup Gal(Ksep/K))]
      fixedField (V : Subgroup Gal(Ksep/K))) := Fintype.ofFinite _
  have hreg : d.toFun (MonoidAlgebra (ZMod l) (fixedField (V : Subgroup Gal(Ksep/K)) ≃ₐ[fixedField
      (U : Subgroup Gal(Ksep/K))] fixedField (V : Subgroup Gal(Ksep/K))))
      (leftRegular (ZMod l) _) = Module.finrank (ULift.{u} (ZMod l)) M := by
    refine (congrArg (fun m : ℕ => (m : ℤ)) (finrank_invariants_zmodRepULift_leftRegular_tprod
      (σ.comp (quotientFixedFieldGalEquiv h).symm.toMonoidHom))).trans ?_
    change ((Module.finrank (ULift.{u} (ZMod l))
      (rootsRepZMod (K := K) (Ksep := Ksep) l U →ₗ[ULift.{u} (ZMod l)] M) : ℕ) : ℤ) = _
    rw [Module.finrank_linearMap, hTr, one_mul]
  rw [hreg] at hg
  have e0' : (_ : ℤ) = d.toFun _ (torsNRep _ (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l) :=
    congrArg (fun m : ℕ => (m : ℤ)) e0
  have e1' : (_ : ℤ) = d.toFun _ (modNRep _ (Additive (fixedField (V : Subgroup Gal(Ksep/K)))ˣ) l) :=
    congrArg (fun m : ℕ => (m : ℤ)) e1
  have e2' : (_ : ℤ) = d.one := congrArg (fun m : ℕ => (m : ℤ)) e2
  linarith [hstep 0, hstep 1, hstep 2]

-- The elaboration of this proof (the cohomology of `U` as twisted invariants of the cohomology
-- of `V`, assembled in degrees 0, 1, 2) exceeds the default limit; raised as in the source.
set_option maxHeartbeats 400000 in
omit [ValuativeRel Ksep] [TopologicalSpace Ksep] [IsValuativeTopology Ksep]
  [ValuativeExtension K Ksep] in

theorem finite_cohomology_coprime (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{u} (ULift.{u} (ZMod l)) (U : Subgroup Gal(Ksep/K))) [IsSmoothRep M]
    [Module.Finite (ULift.{u} (ZMod l)) M]
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    (i : ℕ) (hi : i ≤ 2) : Finite (cohomology M i) := by
  have hlp : l.Prime := Fact.out
  have : CompactSpace (U : Subgroup Gal(Ksep/K)) := compactSpace_openSubgroup U
  have : CompactSpace ((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))) :=
    compactSpace_openSubgroup (openSubgroupOf U V)
  have hT : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))))
      (t : rootsRepZMod (K := K) (Ksep := Ksep) l U),
      (rootsRepZMod (K := K) (Ksep := Ksep) l U).ρ g t = t :=
    rootsRepZMod_ρ_of_mem hμ
  have hM' : ∀ (g : (openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K)))) (m : M),
      M.ρ g m = m :=
    fun g m => hM g (Subgroup.mem_subgroupOf.1 g.2) m
  have hTr : Module.finrank (ULift.{u} (ZMod l)) (rootsRepZMod (K := K) (Ksep := Ksep) l U) = 1 :=
    finrank_rootsRepZMod l hl _
  have hP : (((openSubgroupOf U V : Subgroup (U : Subgroup Gal(Ksep/K))).index :
      ULift.{u} (ZMod l))) ≠ 0 := fun h0 => by
    have h0' : (((V : Subgroup Gal(Ksep/K)).relIndex U : ℕ) : ZMod l) = 0 := congrArg ULift.down h0
    rw [ZMod.natCast_eq_zero_iff] at h0'
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hcop.symm h0'
  have : Finite (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
      (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i) := by
    have := finite_cohomology_roots_subgroupOf (K := K) (Ksep := Ksep) hl h i hi
    exact Finite.of_equiv _ (rootsCohomologyZModEquiv (K := K) (Ksep := Ksep) (U := U) (V := V)
      l i).toEquiv
  have : Module.Finite (ULift.{u} (ZMod l)) (cohomology (Rep.res ((V : Subgroup Gal(Ksep/K)).subgroupOf
      (U : Subgroup Gal(Ksep/K))).subtype (rootsRepZMod (K := K) (Ksep := Ksep) l U)) i) :=
    Module.Finite.of_finite
  have : Module.Finite (ULift.{u} (ZMod l)) (rootsRepZMod (K := K) (Ksep := Ksep) l U) :=
    Module.finite_of_finrank_eq_succ hTr
  have : Module.Finite (ULift.{u} (ZMod l)) (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M) :=
    inferInstanceAs (Module.Finite (ULift.{u} (ZMod l))
      (rootsRepZMod (K := K) (Ksep := Ksep) l U →ₗ[ULift.{u} (ZMod l)] M))
  have : NeZero l := ⟨hlp.ne_zero⟩
  have : Finite (ULift.{u} (ZMod l)) := Finite.of_equiv (ZMod l) Equiv.ulift.symm
  have := Module.finite_of_finite (ULift.{u} (ZMod l)) (M := ((cohomologyConjRep
    (rootsRepZMod (K := K) (Ksep := Ksep) l U) (openSubgroupOf U V : Subgroup _) i).tprod
      (quotientRep (openSubgroupOf U V : Subgroup _) (homRep (rootsRepZMod (K := K) (Ksep := Ksep) l U) M)
        (homRep_ρ_of_mem _ _ _ hT hM'))).invariants)
  exact Finite.of_equiv _ (coprimeTwistEquiv (openSubgroupOf U V)
    (rootsRepZMod (K := K) (Ksep := Ksep) l U) M hT hM' hTr hP i).symm.toEquiv

theorem eulerCharacteristic_coprime (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup Gal(Ksep/K))) [IsSmoothRep M] [Finite M]
    (hMl : ∀ m : M, l • m = 0)
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    {n : ℕ} (hn : Nat.card (𝒪[fixedField (U : Subgroup Gal(Ksep/K))] ⧸
      Ideal.span {(l : 𝒪[fixedField (U : Subgroup Gal(Ksep/K))])}) = l ^ n) :
    eulerCharacteristic M = ((Nat.card M : ℚ) ^ n)⁻¹ := by
  have hlp : l.Prime := Fact.out
  set MZ := zmodRepOfTorsion l M hMl
  have : Finite MZ := ‹Finite M›
  have : Module.Finite (ULift.{u} (ZMod l)) MZ := Module.Finite.of_finite
  have hMZ : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : MZ, MZ.ρ g m = m :=
    hM
  have hsum := finrank_cohomology_alternating_sum_coprime hl h hcop hμ MZ hMZ hn
  have hcard : ∀ i ≤ 2,
      Nat.card (cohomology M i) = l ^ Module.finrank (ULift.{u} (ZMod l)) (cohomology MZ i) :=
    fun i hi => by
      have := finite_cohomology_coprime hl h hcop hμ MZ hMZ i hi
      rw [Nat.card_congr (cohomologyZModEquiv l M hMl i).toEquiv, natCard_eq_pow_finrank_zmod l]
  have hcardM : Nat.card M = l ^ Module.finrank (ULift.{u} (ZMod l)) MZ :=
    natCard_eq_pow_finrank_zmod l MZ
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hlp.ne_zero
  rw [eulerCharacteristic_eq, hcard 0 (by norm_num), hcard 1 (by norm_num), hcard 2 (by norm_num), hcardM]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast (_ ^ _), ← zpow_natCast,
    ← zpow_mul, ← zpow_add₀ hl0, ← zpow_sub₀ hl0, ← zpow_neg]
  congr 1
  linarith

omit [ValuativeRel Ksep] [TopologicalSpace Ksep] [IsValuativeTopology Ksep]
  [ValuativeExtension K Ksep] in

theorem finite_cohomology_coprime_of_torsion (hl : (l : K) ≠ 0) (h : V ≤ U)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (U : Subgroup Gal(Ksep/K))).Normal]
    (hcop : Nat.Coprime ((V : Subgroup Gal(Ksep/K)).relIndex U) l)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup Gal(Ksep/K))) [IsSmoothRep M] [Finite M]
    (hMl : ∀ m : M, l • m = 0)
    (hM : ∀ g : (U : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ V → ∀ m : M, M.ρ g m = m)
    (i : ℕ) (hi : i ≤ 2) : Finite (cohomology M i) := by
  have : Finite (zmodRepOfTorsion l M hMl) := ‹Finite M›
  have : Module.Finite (ULift.{u} (ZMod l)) (zmodRepOfTorsion l M hMl) := Module.Finite.of_finite
  have := finite_cohomology_coprime hl h hcop hμ (zmodRepOfTorsion l M hMl) hM i hi
  exact Finite.of_equiv _ (cohomologyZModEquiv l M hMl i).symm.toEquiv

end Main

end Langlands.GaloisCohomology.Local
