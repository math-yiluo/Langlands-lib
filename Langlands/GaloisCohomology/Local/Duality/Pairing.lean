import Langlands.Cohomology.Profinite.Duality.Main
import Langlands.GaloisCohomology.Field.CartierDual
import Langlands.GaloisCohomology.Local.Dimension
import Langlands.GaloisCohomology.Local.Duality.KummerCup
import Langlands.GaloisCohomology.Local.Duality.NormCharacters

/-!
# The local Tate pairing, and duality from a counting hypothesis

For a nonarchimedean local field `K` with separable closure `Ksep`, the local Tate pairing of a
finite smooth module `M` is the cup product with values in `H²(Gal(Ksep/K), Ksepˣ)` followed by the
invariant: `tatePairing K Ksep M h : Hʳ(M) × Hˢ(M') → ℚ/ℤ` for `r + s = 2`, with
`M' = Hom(M, Ksepˣ)` the Cartier dual.

Its perfectness is reduced, through the abstract duality theorem of the foundations
(`DualizingData`, dualizing module `μ_n`), to the perfectness of the cup product
`H¹(U, ℤ/n) × H¹(U, μ_n) → H²(U, μ_n) ≅ ℤ/n` on every open subgroup `U`. Its left kernel vanishes
by the norm index (`eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left`); given the inequality
`|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|` (`CardCohomologyOneLe`, proved with the Euler characteristic in
`Duality/Main.lean`), counting gives perfectness (`isPerfectPairing_rootsOfUnityInvariant`).
-/

noncomputable section

open CategoryTheory MonoidalCategory IntermediateField

namespace Langlands.GaloisCohomology.Local

universe u

open Langlands.ProfiniteCohomology ClassFieldTheory.Local GroupCoh

section Degree1

variable {K Ksep : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] {n : ℕ}

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep] in
theorem natCast_fixedField_ne_zero (hn : (n : K) ≠ 0) (W : Subgroup Gal(Ksep/K)) :
    (n : fixedField W) ≠ 0 := by
  rw [← map_natCast (algebraMap K (fixedField W))]
  exact (map_ne_zero_iff _ (algebraMap K (fixedField W)).injective).2 hn

/-- The left kernel of `H¹(U, ℤ/n) × H¹(U, μ_n) → H²(U, μ_n)` is zero: a character orthogonal to
every Kummer class has every unit of the fixed field as a norm, hence is trivial by the norm
index. -/
theorem eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left (hn : (n : K) ≠ 0)
    (U : OpenSubgroup Gal(Ksep/K)) (x : cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)
    (h : ∀ y : cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (rootsOfUnityModule K Ksep n)) 1,
      cupPairing (zmodMulPairing n (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
        (rootsOfUnityModule K Ksep n))
        (nsmul_res_rootsOfUnityModule_eq_zero hn _)) (show 1 + 1 = 2 from rfl) x y = 0) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
  have hnorm := fun a => (cupPairing_δ_unitsInvariantOpen_eq_zero_iff hn U z a).1 (h _)
  have hopen : IsOpen (charKer (charAdd (openChar n U z)) :
      Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) := by
    have e : (charKer (charAdd (openChar n U z)) :
        Set Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K)))) =
        (fun g => openChar n U z (Additive.ofMul g)) ⁻¹' {0} := by
      ext g
      exact mem_charKer
    rw [e]
    exact (isOpen_discrete _).preimage ((openChar n U z).continuous_toFun.comp continuous_ofMul)
  have hcomm : ∀ σ τ : Gal(Ksep/fixedField (U : Subgroup Gal(Ksep/K))),
      σ * τ * σ⁻¹ * τ⁻¹ ∈ charKer (charAdd (openChar n U z)) := fun σ τ => by
    rw [mem_charKer, ofMul_mul, ofMul_mul, ofMul_mul, ofMul_inv, ofMul_inv, map_add, map_add,
      map_add, map_neg, map_neg]
    abel
  let := LocalField.FiniteExtension.normedField K (fixedField (U : Subgroup Gal(Ksep/K)))
  let := LocalField.FiniteExtension.valuativeRel K (fixedField (U : Subgroup Gal(Ksep/K)))
  let := LocalField.FiniteExtension.isLocalField K (fixedField (U : Subgroup Gal(Ksep/K)))
  have htop := eq_top_of_forall_exists_norm _ hopen hcomm hnorm
  rw [cohomologyπ_one_eq_zero_iff_of_trivial _ (fun _ _ => rfl)]
  exact fun g => ULift.ext (zmodCocycleHom_eq_zero_of_charKer_eq_top hn U z htop g)

variable (K Ksep) in
/-- The counting hypothesis of local duality in degree one: `|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|` for every
open subgroup `U` and every `n` invertible in `K`. It follows from the local Euler characteristic
formula (`cardCohomologyOneLe`, in `Duality/Main.lean`). -/
def CardCohomologyOneLe : Prop :=
  ∀ (n : ℕ), (n : K) ≠ 0 → ∀ U : OpenSubgroup Gal(Ksep/K),
    Nat.card (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep n)) 1) ≤
      Nat.card (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)

/-- The cup product `H¹(U, ℤ/n) × H¹(U, μ_n) → H²(U, μ_n) ≅ ℤ/n` is a perfect pairing, given
`|H¹(U, μ_n)| ≤ |H¹(U, ℤ/n)|`. -/
theorem isPerfectPairing_rootsOfUnityInvariant (hn : (n : K) ≠ 0) (U : OpenSubgroup Gal(Ksep/K))
    (hcard : Nat.card (cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype
      (rootsOfUnityModule K Ksep n)) 1) ≤
      Nat.card (cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1)) :
    IsPerfectPairing
      (bilinAddHom (cupPairing (zmodMulPairing n
        (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n))
        (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_rootsOfUnityModule hn)))
        (show 1 + 1 = 2 from rfl)))
      (rootsOfUnityInvariant hn U).toAddMonoidHom := by
  have : NeZero n := ⟨fun h0 => hn (by simp [h0])⟩
  set X := cohomology (zmodRep.{u} (U : Subgroup Gal(Ksep/K)) n) 1
  set Y := cohomology (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n)) 1
  set β := bilinAddHom (cupPairing (zmodMulPairing n
    (Rep.res (U : Subgroup Gal(Ksep/K)).subtype (rootsOfUnityModule K Ksep n))
    (nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_rootsOfUnityModule hn)))
    (show 1 + 1 = 2 from rfl)) with hβ
  set t := (rootsOfUnityInvariant hn U).toAddMonoidHom with ht
  have ht0 : ∀ c, t c = 0 → c = 0 := fun c hc =>
    (rootsOfUnityInvariant hn U).injective (hc.trans (map_zero _).symm)
  have hYfin : Finite Y := finite_cohomology_one_res_rootsOfUnityModule K Ksep hn U
  have hY : ∀ y : Y, n • y = 0 := nsmul_cohomology_eq_zero _
    (nsmul_res_rootsOfUnityModule_eq_zero hn _) 1
  have hX : ∀ x : X, n • x = 0 := nsmul_cohomology_eq_zero _ (nsmul_zmodRep_eq_zero _ n) 1
  have h1 : Function.Injective fun x : X => t.comp (β x) := by
    refine (injective_iff_map_eq_zero (AddMonoidHom.mk' (fun x : X => t.comp (β x))
      (fun a b => by ext; simp))).2 fun x hx => ?_
    refine eq_zero_of_forall_cupPairing_zmodMul_eq_zero_left hn U x fun y => ht0 _ ?_
    exact DFunLike.congr_fun hx y
  have hXfin : Finite X := Finite.of_injective _ h1
  have c1 : Nat.card X ≤ Nat.card (Y →+ ZMod n) := Nat.card_le_card_of_injective _ h1
  have c3 := card_addMonoidHom_zmod_le (n := n) (A := Y)
  have hb1 : Function.Bijective fun x : X => t.comp (β x) :=
    h1.bijective_of_nat_card_le (c3.trans hcard)
  have h2 : Function.Injective fun y : Y => t.comp (β.flip y) := by
    refine (injective_iff_map_eq_zero (AddMonoidHom.mk' (fun y : Y => t.comp (β.flip y))
      (fun a b => by ext; simp))).2 fun y hy => ?_
    by_contra hy0
    obtain ⟨f, hf⟩ := zmod_exists_apply_ne_zero hY hy0
    obtain ⟨x, hx⟩ := hb1.2 f
    apply hf
    rw [← hx]
    exact DFunLike.congr_fun hy x
  have c2 : Nat.card Y ≤ Nat.card (X →+ ZMod n) := Nat.card_le_card_of_injective _ h2
  have c4 := card_addMonoidHom_zmod_le (n := n) (A := X)
  exact ⟨hb1, h2.bijective_of_nat_card_le (c4.trans (c1.trans c3))⟩

variable (K Ksep) in
/-- The dualizing data of the local duality theorem: the dualizing module `μ_n`, finiteness and
vanishing in degree `3`, the invariants `H²(U, μ_n) ≃ ℤ/n` and the perfect pairing in degree `1`
(given the counting hypothesis). -/
def localDualizingData (hn : (n : K) ≠ 0) (hcard : CardCohomologyOneLe K Ksep) :
    DualizingData n (rootsOfUnityModule K Ksep n) where
  nonempty_addEquiv := nonempty_addEquiv_rootsOfUnityModule hn
  finite_cohomology := fun U M _ _ hM r hr => finite_cohomology_res_of_le_two K Ksep hn U M hM r hr
  subsingleton_cohomology_three := fun U M _ _ hM =>
    subsingleton_cohomology_res_of_three_le K Ksep hn U M hM (le_refl 3)
  t := rootsOfUnityInvariant hn
  t_cores := rootsOfUnityInvariant_coresOfLE hn
  isPerfectPairing := fun U => isPerfectPairing_rootsOfUnityInvariant hn U (hcard n hn U)

theorem localDualizingData_t (hn : (n : K) ≠ 0) (hcard : CardCohomologyOneLe K Ksep)
    (U : OpenSubgroup Gal(Ksep/K)) :
    (localDualizingData K Ksep hn hcard).t U = rootsOfUnityInvariant hn U :=
  rfl

end Degree1

section Transport

variable {n : ℕ} [NeZero n]

theorem bijective_of_zmodToQZ {X X' Y Y' : Type*} [AddCommGroup X] [AddCommGroup X']
    [AddCommGroup Y] [AddCommGroup Y'] (β : X →+ Y →+ ZMod n) (γ : X' →+ Y' →+ QZ)
    (e₁ : X ≃+ X') (e₂ : Y ≃+ Y') (hY : ∀ y : Y, n • y = 0)
    (hγ : ∀ x y, γ (e₁ x) (e₂ y) = zmodToQZ n (β x y)) (hβ : Function.Bijective β) :
    Function.Bijective γ := by
  refine ⟨fun x₁ x₂ hx => ?_, fun χ => ?_⟩
  · obtain ⟨a₁, rfl⟩ := e₁.surjective x₁
    obtain ⟨a₂, rfl⟩ := e₁.surjective x₂
    refine congrArg e₁ (hβ.1 (AddMonoidHom.ext fun y => zmodToQZ_injective ?_))
    rw [← hγ, ← hγ, hx]
  · have hχ : ∀ y, n • (χ.comp e₂.toAddMonoidHom) y = 0 := fun y => by
      rw [← map_nsmul, hY, map_zero]
    obtain ⟨x, hx⟩ := hβ.2 (zmodOfQZ _ hχ)
    refine ⟨e₁ x, AddMonoidHom.ext fun y' => ?_⟩
    obtain ⟨y, rfl⟩ := e₂.surjective y'
    rw [hγ, hx, zmodToQZ_zmodOfQZ]
    rfl

end Transport

section CohomologyIso

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The additive isomorphism of cohomology groups induced by an isomorphism of modules. -/
def cohomologyAddEquivOfIso {A B : Rep k G} [IsSmoothRep A] [IsSmoothRep B] (e : A ≅ B)
    (m : ℕ) : cohomology A m ≃+ cohomology B m where
  toFun := (coeffMap e.hom m).hom
  invFun := (coeffMap e.inv m).hom
  left_inv x := by
    rw [← ModuleCat.comp_apply, ← coeffMap_comp, e.hom_inv_id, coeffMap_id]
    rfl
  right_inv x := by
    rw [← ModuleCat.comp_apply, ← coeffMap_comp, e.inv_hom_id, coeffMap_id]
    rfl
  map_add' := map_add _

theorem cohomologyAddEquivOfIso_apply {A B : Rep k G} [IsSmoothRep A] [IsSmoothRep B]
    (e : A ≅ B) (m : ℕ) (x : cohomology A m) :
    cohomologyAddEquivOfIso e m x = (coeffMap e.hom m).hom x :=
  rfl

end CohomologyIso

section TatePairing

variable (K Ksep : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

/-- **The local Tate pairing** `Hʳ(Gal(Ksep/K), M) × Hˢ(Gal(Ksep/K), M') → ℚ/ℤ` for `r + s = 2`,
with `M' = Hom(M, Ksepˣ)` the Cartier dual: the cup product with values in `H²(Ksepˣ)` followed by
the invariant. -/
def tatePairing (M : Rep IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) :
    cohomology M r →+ cohomology (cartierDual K Ksep M) s →+ RationalModIntegers :=
  (AddMonoidHom.compHom (invariant K Ksep).toAddMonoidHom).comp
    (bilinAddHom (cupPairing (cartierPairing K Ksep M) h))

variable {K Ksep}

theorem tatePairing_apply (M : Rep IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) (x : cohomology M r) (y : cohomology (cartierDual K Ksep M) s) :
    tatePairing K Ksep M h x y = invariant K Ksep (cupPairing (cartierPairing K Ksep M) h x y) :=
  rfl

instance isSmoothRep_dualRep_rootsOfUnityModule (n : ℕ) (M : Rep IntegerScalars.{u} Gal(Ksep/K))
    [IsSmoothRep M] [Finite M] : IsSmoothRep (dualRep (rootsOfUnityModule K Ksep n) M) :=
  isSmoothRep_dualRep _ _

/-- The dual `Hom(M, μ_n)` is the Cartier dual when `M` is killed by `n`. -/
def dualRepRootsOfUnityIso (M : Rep IntegerScalars.{u} Gal(Ksep/K)) (n : ℕ)
    (hM : ∀ m : M, n • m = 0) :
    dualRep (rootsOfUnityModule K Ksep n) M ≅ cartierDual K Ksep M :=
  cartierDualIsoHomRootsOfUnityOfNsmul K Ksep M n hM

@[simp]
theorem dualRepRootsOfUnityIso_hom_apply (M : Rep IntegerScalars.{u} Gal(Ksep/K)) (n : ℕ)
    (hM : ∀ m : M, n • m = 0) (f : M →ₗ[IntegerScalars.{u}] rootsOfUnityModule K Ksep n) (m : M) :
    ((dualRepRootsOfUnityIso M n hM).hom.hom f : M →ₗ[IntegerScalars.{u}] unitsModule K Ksep) m =
      (rootsOfUnityToUnits K Ksep n).hom (f m) :=
  rfl

/-- The invariant of the image of a class of `H²(μ_n)` is its value under `t_⊤`. -/
theorem invariant_rootsOfUnityToUnits {n : ℕ} (hn : (n : K) ≠ 0)
    (hcard : CardCohomologyOneLe K Ksep) (z : cohomology (rootsOfUnityModule K Ksep n) 2) :
    invariant K Ksep ((coeffMap (rootsOfUnityToUnits K Ksep n) 2).hom z) =
      QZ.toRationalModIntegers (zmodToQZ n ((localDualizingData K Ksep hn hcard).tTop z)) := by
  have : NeZero n := ⟨fun h0 => hn (by simp [h0])⟩
  have hres := congrArg (fun φ => φ.hom z) (res_naturality (rootsOfUnityModule K Ksep n)
    (rootsOfUnityToUnits K Ksep n) ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hres
  rw [← classFormation_invEquiv_res_top, ClassFormation.invEquiv_apply]
  congr 1
  change _ = zmodToQZ n (rootsOfUnityInvariant hn ⊤ _)
  rw [zmodToQZ_rootsOfUnityInvariant, rootsOfUnityInv_apply]
  exact congrArg _ hres

theorem tensorHom_dualRepRootsOfUnityIso_cartierPairing (M : Rep IntegerScalars.{u} Gal(Ksep/K))
    {n : ℕ} (hM : ∀ m : M, n • m = 0) :
    (𝟙 M ⊗ₘ (dualRepRootsOfUnityIso M n hM).hom) ≫ cartierPairing K Ksep M =
      evalPairing (rootsOfUnityModule K Ksep n) M ≫ rootsOfUnityToUnits K Ksep n := by
  refine Rep.Hom.ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ?_))
  induction x using TensorProduct.inductionOn with
  | tmul a f => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tatePairing_coeffMap (M : Rep IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M]
    [Finite M] {n : ℕ} (hn : (n : K) ≠ 0) (hcard : CardCohomologyOneLe K Ksep)
    (hM : ∀ m : M, n • m = 0) {r s : ℕ} (h : r + s = 2)
    (x : cohomology M r) (y : cohomology (dualRep (rootsOfUnityModule K Ksep n) M) s) :
    tatePairing K Ksep M h x ((coeffMap (dualRepRootsOfUnityIso M n hM).hom s).hom y) =
      QZ.toRationalModIntegers (zmodToQZ n (dualityMap (rootsOfUnityModule K Ksep n) h
        (localDualizingData K Ksep hn hcard).tTop M x y)) := by
  have hc := cupPairing_cohomologyMap (cartierPairing K Ksep M) (𝟙 M)
    (dualRepRootsOfUnityIso M n hM).hom h x y
  rw [coeffMap_id, ModuleCat.id_apply, tensorHom_dualRepRootsOfUnityIso_cartierPairing] at hc
  rw [tatePairing_apply, hc, dualityMap_apply, ← invariant_rootsOfUnityToUnits hn hcard,
    cohomologyMap_cupPairing]

/-- The cohomology of the Cartier dual of a finite module of order invertible in `K` is finite. -/
theorem finite_cohomology_cartierDual (M : Rep IntegerScalars.{u} Gal(Ksep/K))
    [IsSmoothRep M] [Finite M] (hM : (Nat.card M : K) ≠ 0) (r : ℕ) :
    Finite (cohomology (cartierDual K Ksep M) r) := by
  have hkill : ∀ f : cartierDual K Ksep M, Nat.card M • f = 0 := fun f => by
    let f' : M →ₗ[IntegerScalars.{u}] unitsModule K Ksep := f
    change Nat.card M • f' = 0
    refine LinearMap.ext fun m => ?_
    rw [LinearMap.smul_apply, LinearMap.zero_apply, ← map_nsmul, card_nsmul_eq_zero', map_zero]
  have : IsSmoothRep (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype
      (cartierDual K Ksep M)) := isSmoothRep_res_subtype _ _
  have : Finite (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype
      (cartierDual K Ksep M)) := inferInstanceAs (Finite (cartierDual K Ksep M))
  have := finite_cohomology_res K Ksep hM ⊤
    (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype (cartierDual K Ksep M))
    hkill r
  exact Finite.of_injective _ (bijective_res_top (cartierDual K Ksep M) r).1

/-- Local Tate duality, given the counting hypothesis: the Tate pairing is perfect on the left. -/
theorem tatePairing_bijective_of_card (hcard : CardCohomologyOneLe K Ksep)
    (M : Rep IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M] (hM : (Nat.card M : K) ≠ 0)
    {r s : ℕ} (h : r + s = 2) : Function.Bijective (tatePairing K Ksep M h) := by
  set n := Nat.card M
  have : NeZero n := ⟨fun h0 => hM (by simp [n, h0])⟩
  have hMn : ∀ m : M, n • m = 0 := fun _ => card_nsmul_eq_zero'
  have hD : ∀ d : rootsOfUnityModule K Ksep n, n • d = 0 :=
    nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_rootsOfUnityModule hM)
  exact bijective_of_zmodToQZ
    (dualityMap (rootsOfUnityModule K Ksep n) h (localDualizingData K Ksep hM hcard).tTop M)
    (tatePairing K Ksep M h) (AddEquiv.refl _)
    (cohomologyAddEquivOfIso (dualRepRootsOfUnityIso M n hMn) s)
    (nsmul_cohomology_eq_zero _ (nsmul_dualRep_eq_zero hD) s)
    (fun x y => tatePairing_coeffMap M hM hcard hMn h x y)
    ((localDualizingData K Ksep hM hcard).dualityMap_bijective_of_group M hMn h)

/-- Local Tate duality, given the counting hypothesis: the Tate pairing is perfect on the right. -/
theorem tatePairing_flip_bijective_of_card (hcard : CardCohomologyOneLe K Ksep)
    (M : Rep IntegerScalars.{u} Gal(Ksep/K)) [IsSmoothRep M] [Finite M] (hM : (Nat.card M : K) ≠ 0)
    {r s : ℕ} (h : r + s = 2) : Function.Bijective (tatePairing K Ksep M h).flip := by
  set n := Nat.card M
  have : NeZero n := ⟨fun h0 => hM (by simp [n, h0])⟩
  have hMn : ∀ m : M, n • m = 0 := fun _ => card_nsmul_eq_zero'
  have hD : ∀ d : rootsOfUnityModule K Ksep n, n • d = 0 :=
    nsmul_eq_zero_of_nonempty_addEquiv (nonempty_addEquiv_rootsOfUnityModule hM)
  have : Finite (rootsOfUnityModule K Ksep n) :=
    finite_of_nonempty_addEquiv (nonempty_addEquiv_rootsOfUnityModule hM)
  have : Finite (dualRep (rootsOfUnityModule K Ksep n) M) := finite_dualRep
  have : IsSmoothRep (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype
      (dualRep (rootsOfUnityModule K Ksep n) M)) := isSmoothRep_res_subtype _ _
  have : Finite (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype
      (dualRep (rootsOfUnityModule K Ksep n) M)) :=
    inferInstanceAs (Finite (dualRep (rootsOfUnityModule K Ksep n) M))
  have := finite_cohomology_res K Ksep hM ⊤
    (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype
      (dualRep (rootsOfUnityModule K Ksep n) M))
    (fun f => nsmul_dualRep_eq_zero (D := rootsOfUnityModule K Ksep n) hD f) s
  have hfin : Finite (cohomology (dualRep (rootsOfUnityModule K Ksep n) M) s) :=
    Finite.of_injective _ (bijective_res_top (dualRep (rootsOfUnityModule K Ksep n) M) s).1
  have hΨ := (localDualizingData K Ksep hM hcard).dualityMap_bijective_of_group M hMn h
  have hflip := bijective_of_bijective_flip
    (X := cohomology (dualRep (rootsOfUnityModule K Ksep n) M) s)
    (nsmul_cohomology_eq_zero _ (nsmul_dualRep_eq_zero hD) s)
    (bilinAddHom (cupPairing (evalPairing (rootsOfUnityModule K Ksep n) M) h)).flip
    (localDualizingData K Ksep hM hcard).tTop hΨ
  refine bijective_of_zmodToQZ
    (dualityMap (rootsOfUnityModule K Ksep n) h (localDualizingData K Ksep hM hcard).tTop M).flip
    (tatePairing K Ksep M h).flip
    (cohomologyAddEquivOfIso (dualRepRootsOfUnityIso M n hMn) s) (AddEquiv.refl _)
    (nsmul_cohomology_eq_zero M hMn r)
    (fun y x => tatePairing_coeffMap M hM hcard hMn h x y) ?_
  convert hflip using 1
  funext y
  exact AddMonoidHom.ext fun x => rfl

end TatePairing

end Langlands.GaloisCohomology.Local
