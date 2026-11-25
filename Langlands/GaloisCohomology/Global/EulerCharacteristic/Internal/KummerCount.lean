import Langlands.Cohomology.Profinite.Duality.Devissage
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Descent
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Additive

/-!
# Additive functions on the Kummer sequence of an open normal subgroup

Let `G` be a profinite group, `N` a closed normal subgroup and `0 → T → O → O → 0` a short exact
sequence of smooth `G`-modules whose second map is multiplication by `n`. Restricted to `N`, its
long exact sequence breaks up into the short exact sequences
`0 → Hⁱ(N, O)/n → Hⁱ⁺¹(N, T) → Hⁱ⁺¹(N, O)[n] → 0` and an isomorphism `H⁰(N, T) ≅ H⁰(N, O)[n]`, and
all these maps commute with the conjugation action of `G` (`kummerModNHom`, `kummerTorsHom`).

When `G/N` is identified with a group `Γ` (`e : G ⧸ N ≃* Γ`), the conjugation action makes the
groups `Hⁱ(N, A)` modules over `Γ` (`conjAction`), and an additive function `d` on finite
`𝔽_n[Γ]`-modules satisfies `d(Hⁱ⁺¹(N, T)) = d(Hⁱ(N, O)/n) + d(Hⁱ⁺¹(N, O)[n])`
(`toFun_eq_modN_add_torsN`) and `d(H⁰(N, T)) = d(H⁰(N, O)[n])` (`toFun_eq_torsN_zero`). With `O` the
`S`-units and `T` the roots of unity this is the Kummer step of Tate's proof of the global Euler
characteristic formula.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.GaloisCohomology.Local

universe u

noncomputable section

section Sequence

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) {T O : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep T] [IsSmoothRep O]
  {n : ℕ} {f : T ⟶ O} {w : f ≫ (n • 𝟙 O) = 0} (hS : (ShortComplex.mk f (n • 𝟙 O) w).ShortExact)

/-- Multiplication by `n` on `O` induces multiplication by `n` on `Hⁱ(N, O)`. -/
theorem coeffMap_res_nsmul_id_apply (O : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep O] (n i : ℕ)
    (x : cohomology (Rep.res N.subtype O) i) :
    (coeffMap ((Rep.resFunctor N.subtype).map (n • 𝟙 O)) i).hom x = n • x := by
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
  exact cohomologyMap_nsmul_id_apply _ n i x

include w in
/-- The image of `Hⁱ(N, T) → Hⁱ(N, O)` is killed by `n`. -/
theorem nsmul_coeffMap_res_f_apply (i : ℕ) (x : cohomology (Rep.res N.subtype T) i) :
    n • (coeffMap ((Rep.resFunctor N.subtype).map f) i).hom x = 0 := by
  rw [← coeffMap_res_nsmul_id_apply N O n i]
  exact congrArg (fun φ => φ.hom x)
    (map_f_comp_g (S := (ShortComplex.mk f (n • 𝟙 O) w).map (Rep.resFunctor N.subtype)) i)

/-- The connecting map kills `n Hⁱ(N, O)`. -/
theorem δ_res_nsmul_apply (i : ℕ) (y : cohomology (Rep.res N.subtype O) i) :
    (δ (shortExact_map_res N hS) i (i + 1) rfl).hom (n • y) = 0 := by
  rw [← coeffMap_res_nsmul_id_apply N O n i]
  exact congrArg (fun φ => φ.hom y) (comp_δ (shortExact_map_res N hS) i (i + 1) rfl)

variable (w) in
/-- The map `Hⁱ(N, T) → Hⁱ(N, O)[n]`. -/
def kummerTorsHom (i : ℕ) :
    cohomology (Rep.res N.subtype T) i →+ TorsN (cohomology (Rep.res N.subtype O) i) n where
  toFun x := ⟨(coeffMap ((Rep.resFunctor N.subtype).map f) i).hom x,
    (mem_ker_lsmul_iff n _).2 (nsmul_coeffMap_res_f_apply N (w := w) i x)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp]
theorem coe_kummerTorsHom_apply (i : ℕ) (x : cohomology (Rep.res N.subtype T) i) :
    ((kummerTorsHom N w i x : TorsN _ n) : cohomology (Rep.res N.subtype O) i) =
      (coeffMap ((Rep.resFunctor N.subtype).map f) i).hom x :=
  rfl

theorem range_lsmul_le_ker_δ (i : ℕ) :
    LinearMap.range (LinearMap.lsmul ℤ (cohomology (Rep.res N.subtype O) i) (n : ℤ)) ≤
      LinearMap.ker (δ (shortExact_map_res N hS) i (i + 1) rfl).hom.toAddMonoidHom.toIntLinearMap := by
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, natCast_zsmul, AddMonoidHom.coe_toIntLinearMap]
  exact δ_res_nsmul_apply N hS i y

/-- The map `Hⁱ(N, O)/n → Hⁱ⁺¹(N, T)` induced by the connecting map. -/
def kummerModNHom (i : ℕ) :
    ModN (cohomology (Rep.res N.subtype O) i) n →+ cohomology (Rep.res N.subtype T) (i + 1) :=
  ((LinearMap.range (LinearMap.lsmul ℤ (cohomology (Rep.res N.subtype O) i) (n : ℤ))).liftQ
    (δ (shortExact_map_res N hS) i (i + 1) rfl).hom.toAddMonoidHom.toIntLinearMap
    (range_lsmul_le_ker_δ N hS i)).toAddMonoidHom

theorem kummerModNHom_mk (i : ℕ) (y : cohomology (Rep.res N.subtype O) i) :
    kummerModNHom N hS i (Submodule.Quotient.mk y) = (δ (shortExact_map_res N hS) i (i + 1) rfl).hom y :=
  rfl

theorem range_lsmul_eq_ker_δ (i : ℕ) :
    LinearMap.range (LinearMap.lsmul ℤ (cohomology (Rep.res N.subtype O) i) (n : ℤ)) =
      LinearMap.ker (δ (shortExact_map_res N hS) i (i + 1) rfl).hom.toAddMonoidHom.toIntLinearMap := by
  refine le_antisymm (range_lsmul_le_ker_δ N hS i) fun y hy => ?_
  rw [LinearMap.mem_ker, AddMonoidHom.coe_toIntLinearMap] at hy
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₃ (shortExact_map_res N hS) i (i + 1) rfl) y hy
  let z' : cohomology (Rep.res N.subtype O) i := z
  have hz' : (coeffMap ((Rep.resFunctor N.subtype).map (n • 𝟙 O)) i).hom z' = y := hz
  refine ⟨z', ?_⟩
  change (n : ℤ) • z' = y
  rw [natCast_zsmul, ← coeffMap_res_nsmul_id_apply N O n i]
  exact hz'

theorem kummerModNHom_injective (i : ℕ) : Function.Injective (kummerModNHom N hS i) := by
  change Function.Injective ((LinearMap.range (LinearMap.lsmul ℤ
    (cohomology (Rep.res N.subtype O) i) (n : ℤ))).liftQ
    (δ (shortExact_map_res N hS) i (i + 1) rfl).hom.toAddMonoidHom.toIntLinearMap
    (range_lsmul_le_ker_δ N hS i))
  rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
  exact range_lsmul_eq_ker_δ N hS i

include hS in
theorem kummerTorsHom_surjective (i : ℕ) : Function.Surjective (kummerTorsHom N w i) := by
  rintro ⟨y, hy⟩
  have hy' : (coeffMap ((Rep.resFunctor N.subtype).map (n • 𝟙 O)) i).hom y = 0 := by
    rw [coeffMap_res_nsmul_id_apply]
    exact (mem_ker_lsmul_iff n y).1 hy
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (cohomology_exact₂ (shortExact_map_res N hS) i) y hy'
  exact ⟨x, Subtype.ext hx⟩

theorem kummerTorsHom_eq_zero_iff (i : ℕ) (x : cohomology (Rep.res N.subtype T) (i + 1)) :
    kummerTorsHom N w (i + 1) x = 0 ↔ ∃ y, kummerModNHom N hS i y = x := by
  constructor
  · intro hx
    have hx' : (coeffMap ((Rep.resFunctor N.subtype).map f) (i + 1)).hom x = 0 :=
      congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (cohomology_exact₁ (shortExact_map_res N hS) i (i + 1) rfl) x hx'
    exact ⟨Submodule.Quotient.mk y, hy⟩
  · rintro ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      apply Subtype.ext
      exact congrArg (fun φ => φ.hom y) (δ_comp (shortExact_map_res N hS) i (i + 1) rfl)

include hS in
theorem kummerTorsHom_bijective_zero : Function.Bijective (kummerTorsHom N w 0) := by
  have hf : Function.Injective f.hom := (Rep.mono_iff_injective f).1 hS.mono_f
  have hf' : Function.Injective ((Rep.resFunctor N.subtype).map f).hom := hf
  exact ⟨fun _ _ hxy => injective_cohomologyMap_zero _ hf' (congrArg Subtype.val hxy),
    kummerTorsHom_surjective N hS 0⟩

variable [N.Normal]

theorem kummerTorsHom_cohomologyConj (i : ℕ) (g : G) (x : cohomology (Rep.res N.subtype T) i) :
    ((kummerTorsHom N w i ((cohomologyConj T N i g).hom x) : TorsN _ n) :
        cohomology (Rep.res N.subtype O) i) =
      (cohomologyConj O N i g).hom (kummerTorsHom N w i x) :=
  (congrArg (fun φ => φ.hom x) (cohomologyConj_naturality T N f i g)).symm

theorem kummerModNHom_cohomologyConj (i : ℕ) (g : G) (y : cohomology (Rep.res N.subtype O) i) :
    kummerModNHom N hS i (Submodule.Quotient.mk ((cohomologyConj O N i g).hom y)) =
      (cohomologyConj T N (i + 1) g).hom (kummerModNHom N hS i (Submodule.Quotient.mk y)) :=
  (congrArg (fun φ => φ.hom y) (δ_comp_cohomologyConj N hS i (i + 1) rfl g)).symm

end Sequence

section Action

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal] [CompactSpace N] {Γ : Type*} [Group Γ] (e : G ⧸ N ≃* Γ)

/-- The conjugation action of `Γ ≅ G/N` on `Hⁱ(N, A)`. -/
abbrev conjAction {k : Type u} [CommRing k] (A : Rep.{u} k G) [IsSmoothRep A] (i : ℕ) :
    DistribMulAction Γ (cohomology (Rep.res N.subtype A) i) where
  smul γ x := cohomologyConjRep A N i (e.symm γ) x
  one_smul x := by
    change cohomologyConjRep A N i (e.symm 1) x = x
    rw [map_one, map_one, Module.End.one_apply]
  mul_smul γ δ x := by
    change cohomologyConjRep A N i (e.symm (γ * δ)) x =
      cohomologyConjRep A N i (e.symm γ) (cohomologyConjRep A N i (e.symm δ) x)
    rw [map_mul, map_mul, Module.End.mul_apply]
  smul_zero _ := map_zero _
  smul_add _ _ _ := map_add _ _ _

theorem conjAction_smul {k : Type u} [CommRing k] (A : Rep.{u} k G) [IsSmoothRep A] (i : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype A) i) :
    (letI := conjAction N e A i; e (QuotientGroup.mk g) • x) = (cohomologyConj A N i g).hom x := by
  change cohomologyConjRep A N i (e.symm (e (QuotientGroup.mk g))) x = _
  rw [MulEquiv.symm_apply_apply, cohomologyConjRep_mk]

variable {T O : Rep.{u} (ULift.{u} ℤ) G} [IsSmoothRep T] [IsSmoothRep O]
  {l : ℕ} {f : T ⟶ O} {w : f ≫ (l • 𝟙 O) = 0} (hS : (ShortComplex.mk f (l • 𝟙 O) w).ShortExact)

include hS in
/-- **Kummer in degree `i + 1`.** For an additive function `d` on `𝔽_l[Γ]`-modules and a model `X`
of `Hⁱ⁺¹(N, T)` as a `Γ`-module, `d(X) = d(Hⁱ(N, O)/l) + d(Hⁱ⁺¹(N, O)[l])`. -/
theorem toFun_eq_modN_add_torsN (d : AdditiveFunction.{u} l Γ) (i : ℕ)
    [Finite (ModN (cohomology (Rep.res N.subtype O) i) l)]
    [Finite (TorsN (cohomology (Rep.res N.subtype O) (i + 1)) l)]
    {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X] (ρX : Representation (ZMod l) Γ X)
    (φ : X ≃+ cohomology (Rep.res N.subtype T) (i + 1))
    (hφ : ∀ (g : G) (x : X), φ (ρX (e (QuotientGroup.mk g)) x) = (cohomologyConj T N (i + 1) g).hom (φ x)) :
    d.toFun X ρX =
      (letI := conjAction N e O i;
        d.toFun (ModN (cohomology (Rep.res N.subtype O) i) l)
          (modNRep Γ (cohomology (Rep.res N.subtype O) i) l)) +
      (letI := conjAction N e O (i + 1);
        d.toFun (TorsN (cohomology (Rep.res N.subtype O) (i + 1)) l)
          (torsNRep Γ (cohomology (Rep.res N.subtype O) (i + 1)) l)) := by
  let := conjAction N e O i
  let := conjAction N e O (i + 1)
  have hsurj : ∀ γ : Γ, ∃ g : G, e (QuotientGroup.mk g) = γ := fun γ => by
    obtain ⟨q, rfl⟩ := e.surjective γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨g, rfl⟩
  have hφ' : ∀ (g : G) (y : cohomology (Rep.res N.subtype T) (i + 1)),
      φ.symm ((cohomologyConj T N (i + 1) g).hom y) = ρX (e (QuotientGroup.mk g)) (φ.symm y) :=
    fun g y => by
      apply φ.injective
      rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let a : ModN (cohomology (Rep.res N.subtype O) i) l →ₗ[ZMod l] X :=
    ((φ.symm.toAddMonoidHom).comp (kummerModNHom N hS i)).toZModLinearMap l
  let b : X →ₗ[ZMod l] TorsN (cohomology (Rep.res N.subtype O) (i + 1)) l :=
    ((kummerTorsHom N w (i + 1)).comp φ.toAddMonoidHom).toZModLinearMap l
  refine d.additive _ ρX _ a b ⟨fun γ y => ?_⟩ ⟨fun γ x => ?_⟩ ?_ ?_ ?_
  · obtain ⟨g, rfl⟩ := hsurj γ
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      change φ.symm (kummerModNHom N hS i (Submodule.Quotient.mk (e (QuotientGroup.mk g) • y))) =
        ρX (e (QuotientGroup.mk g)) (φ.symm (kummerModNHom N hS i (Submodule.Quotient.mk y)))
      rw [conjAction_smul, kummerModNHom_cohomologyConj, hφ']
  · obtain ⟨g, rfl⟩ := hsurj γ
    apply Subtype.ext
    change ((kummerTorsHom N w (i + 1) (φ (ρX (e (QuotientGroup.mk g)) x)) : TorsN _ l) :
        cohomology (Rep.res N.subtype O) (i + 1)) =
      e (QuotientGroup.mk g) • ((kummerTorsHom N w (i + 1) (φ x) : TorsN _ l) :
        cohomology (Rep.res N.subtype O) (i + 1))
    rw [hφ, kummerTorsHom_cohomologyConj, conjAction_smul]
  · exact φ.symm.injective.comp (kummerModNHom_injective N hS i)
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := (kummerTorsHom_eq_zero_iff N hS i (φ x)).1 hx
      refine ⟨y, ?_⟩
      change φ.symm (kummerModNHom N hS i y) = x
      rw [hy, AddEquiv.symm_apply_apply]
    · rintro ⟨y, rfl⟩
      change kummerTorsHom N w (i + 1) (φ (φ.symm (kummerModNHom N hS i y))) = 0
      rw [AddEquiv.apply_symm_apply]
      exact (kummerTorsHom_eq_zero_iff N hS i _).2 ⟨y, rfl⟩
  · intro z
    obtain ⟨x, hx⟩ := kummerTorsHom_surjective N hS (i + 1) z
    exact ⟨φ.symm x, by
      change kummerTorsHom N w (i + 1) (φ (φ.symm x)) = z
      rw [AddEquiv.apply_symm_apply, hx]⟩

include hS in
/-- **Kummer in degree `0`.** `d(H⁰(N, T)) = d(H⁰(N, O)[l])`. -/
theorem toFun_eq_torsN_zero (d : AdditiveFunction.{u} l Γ)
    [Finite (TorsN (cohomology (Rep.res N.subtype O) 0) l)]
    {X : Type u} [AddCommGroup X] [Module (ZMod l) X] [Finite X] (ρX : Representation (ZMod l) Γ X)
    (φ : X ≃+ cohomology (Rep.res N.subtype T) 0)
    (hφ : ∀ (g : G) (x : X), φ (ρX (e (QuotientGroup.mk g)) x) = (cohomologyConj T N 0 g).hom (φ x)) :
    d.toFun X ρX =
      (letI := conjAction N e O 0;
        d.toFun (TorsN (cohomology (Rep.res N.subtype O) 0) l)
          (torsNRep Γ (cohomology (Rep.res N.subtype O) 0) l)) := by
  let := conjAction N e O 0
  let E : X ≃+ TorsN (cohomology (Rep.res N.subtype O) 0) l :=
    φ.trans (AddEquiv.ofBijective (kummerTorsHom N w 0) (kummerTorsHom_bijective_zero N hS))
  refine d.toFun_congr _ _
    { (E.toAddMonoidHom.toZModLinearMap l) with
      invFun := E.symm, left_inv := E.left_inv, right_inv := E.right_inv } fun γ x => ?_
  obtain ⟨q, rfl⟩ := e.surjective γ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  apply Subtype.ext
  change ((kummerTorsHom N w 0 (φ (ρX (e (QuotientGroup.mk g)) x)) : TorsN _ l) :
      cohomology (Rep.res N.subtype O) 0) =
    e (QuotientGroup.mk g) • ((kummerTorsHom N w 0 (φ x) : TorsN _ l) :
      cohomology (Rep.res N.subtype O) 0)
  rw [hφ, kummerTorsHom_cohomologyConj, conjAction_smul]

end Action

end

end Langlands.GaloisCohomology
