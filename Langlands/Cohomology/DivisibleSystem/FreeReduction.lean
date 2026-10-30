import Langlands.Cohomology.DivisibleSystem.FreeRestrictScalars
import Langlands.Cohomology.DivisibleSystem.Reduction

/-!
# Reductions of free representations

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, proof of
Proposition 4.10, p.312: "Since `C^j_m(ẽ)^{H_p}` and `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` are both free
`𝒪/ℓ^m𝒪[S(ẽ)/H_p]`-modules, it follows that the maps (4.10.3) are surjective for all `m`."
The published predicate `FreeOverPowQuotient ℓ m` expresses this freeness for a representation
over `R` (Harris's `𝒪`), and the published `reductionSystem ℓ L` is the `ℓ`-divisible system of
the reductions `L / ℓ ^ m L` (Harris's `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m`, p.311). This module shows that
reduction modulo `ℓ ^ m` turns a representation free over `R[G]` into one free over
`(R ⧸ (ℓ ^ m))[G]`, so that the reduction system of such a representation satisfies the
hypothesis of the published Hom-system results.

* `coeffReduction`, `freeReductionAddHom`, `freeReductionLinearMap`, `freeReduction`: reduction
  of coefficients `α →₀ R[G] → α →₀ (R ⧸ (ℓ ^ m))[G]`, as a morphism in `Rep R G` into the
  restriction of scalars of the free representation over `R ⧸ (ℓ ^ m)`;
* `freeReduction_surjective`, `exists_pow_smul_of_freeReduction_eq_zero`,
  `freeReductionComplex_exact`, `cokernelFreeIso`: reduction is surjective with kernel the
  image of multiplication by `ℓ ^ m`, so it identifies the cokernel of `ℓ ^ m`;
* `freeOverPowQuotient_cokernel_powSMul_free`, `isoFreeOfFree`,
  `freeOverPowQuotient_cokernel_powSMul_of_free`: for `P` free over `R[G]`, the cokernel of
  multiplication by `ℓ ^ m` on `P` satisfies `FreeOverPowQuotient ℓ m`;
* `isSMulRegular_free`, `mono_powSMul_free`, `mono_powSMul_of_free`: if `ℓ` is a
  non-zero-divisor in `R`, multiplication by `ℓ` on such a `P` is a monomorphism;
* `freeOverPowQuotient_reductionSystem_obj`, `homSystem_reductionSystem_map_surjective`,
  `isMittagLeffler_homSystem_reductionSystem`: the consequences for `reductionSystem ℓ P`.

The module does not prove that Harris's modules `C^j_m(ẽ)^{H_p}` are reductions of
representations free over `𝒪[S(ẽ)/H_p]`. The definitions and proofs are ours.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits

universe w u v

section FreeRep

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] (ℓ m : ℕ)

/-- Reduction modulo `ℓ ^ m` of the coefficients of an element of `R[G]`. -/
def coeffReduction :
    MonoidAlgebra R G →+ MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G where
  toFun := MonoidAlgebra.map (Ideal.Quotient.mk (Ideal.span {((ℓ : R) ^ m)})).toAddMonoidHom
  map_zero' := MonoidAlgebra.map_zero _
  map_add' := MonoidAlgebra.map_add _

omit [Monoid G] in
/-- The coefficients of `coeffReduction ℓ m z` are the classes of those of `z`. -/
lemma coeffReduction_coeff (z : MonoidAlgebra R G) (g : G) :
    (coeffReduction ℓ m z).coeff g = Ideal.Quotient.mk _ (z.coeff g) :=
  rfl

omit [Monoid G] in
/-- `coeffReduction ℓ m` sends `single g r` to `single g` of the class of `r`. -/
lemma coeffReduction_single (g : G) (r : R) :
    coeffReduction ℓ m (MonoidAlgebra.single g r) =
      MonoidAlgebra.single g (Ideal.Quotient.mk _ r) :=
  MonoidAlgebra.map_single _ r g

variable (α : Type w)

/-- Reduction modulo `ℓ ^ m` of the coefficients of `α →₀ R[G]`. -/
def freeReductionAddHom :
    (α →₀ MonoidAlgebra R G) →+ (α →₀ MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G) :=
  Finsupp.mapRange.addMonoidHom (coeffReduction ℓ m)

/-- The coefficients of `freeReductionAddHom ℓ m α x` are the classes of those of `x`. -/
lemma freeReductionAddHom_coeff (x : α →₀ MonoidAlgebra R G) (a : α) (g : G) :
    ((freeReductionAddHom ℓ m α x) a).coeff g = Ideal.Quotient.mk _ ((x a).coeff g) :=
  rfl

variable {α} in
/-- `freeReductionAddHom ℓ m α` sends `single a (single h r)` to `single a (single h r̄)`, with
`r̄` the class of `r`. -/
lemma freeReductionAddHom_single (a : α) (h : G) (r : R) :
    freeReductionAddHom ℓ m α (Finsupp.single a (MonoidAlgebra.single h r)) =
      Finsupp.single a (MonoidAlgebra.single h (Ideal.Quotient.mk _ r)) := by
  rw [freeReductionAddHom, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
    coeffReduction_single]

/-- Reduction of coefficients commutes with the action of `G` on the free representations. -/
lemma freeReductionAddHom_free (g : G) (x : α →₀ MonoidAlgebra R G) :
    freeReductionAddHom ℓ m α (Representation.free R G α g x) =
      Representation.free (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G α g (freeReductionAddHom ℓ m α x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single a b =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp only [Finsupp.single_zero, map_zero]
    | add b c hb hc => simp only [Finsupp.single_add, map_add, hb, hc]
    | single h r =>
      rw [Representation.free_single_single, freeReductionAddHom_single,
        freeReductionAddHom_single, Representation.free_single_single]

/-- Reduction modulo `ℓ ^ m` of the coefficients of `α →₀ R[G]`, as an `R`-linear map into the
restriction of scalars of `α →₀ (R ⧸ (ℓ ^ m))[G]`. -/
def freeReductionLinearMap :
    (α →₀ MonoidAlgebra R G) →ₗ[R] RestrictScalars R (R ⧸ Ideal.span {((ℓ : R) ^ m)})
      (α →₀ MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G) where
  toFun x := (RestrictScalars.addEquiv R _ _).symm (freeReductionAddHom ℓ m α x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    apply (RestrictScalars.addEquiv R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) _).injective
    rw [RestrictScalars.addEquiv_map_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      RingHom.id_apply]
    ext a g
    rw [freeReductionAddHom_coeff, Finsupp.smul_apply, Finsupp.smul_apply,
      MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_smul_apply, freeReductionAddHom_coeff,
      smul_eq_mul, Ideal.Quotient.algebraMap_eq, smul_eq_mul, map_mul]

attribute [local instance] restrictScalarsModule

/-- Reduction modulo `ℓ ^ m` of the coefficients, as a morphism from the free representation
`α →₀ R[G]` over `R` to the restriction of scalars of the free representation
`α →₀ (R ⧸ (ℓ ^ m))[G]` over `R ⧸ (ℓ ^ m)`. -/
def freeReduction :
    Rep.free R G α ⟶ (repRestrictScalars.{max w u v} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G).obj
      (Rep.free (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G α) :=
  Rep.ofHom ⟨freeReductionLinearMap ℓ m α, fun g => LinearMap.ext fun x =>
    congrArg (RestrictScalars.addEquiv R (R ⧸ Ideal.span {((ℓ : R) ^ m)})
      (α →₀ MonoidAlgebra (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G)).symm
      (freeReductionAddHom_free ℓ m α g x)⟩

/-- The underlying map of `freeReduction ℓ m α` is `freeReductionLinearMap ℓ m α`. -/
lemma freeReduction_hom_apply (x : α →₀ MonoidAlgebra R G) :
    (freeReduction ℓ m α).hom x = freeReductionLinearMap ℓ m α x :=
  rfl

/-- Multiplication by `ℓ ^ m` followed by reduction modulo `ℓ ^ m` is zero. -/
lemma powSMul_comp_freeReduction : powSMul ℓ m (Rep.free R G α) ≫ freeReduction ℓ m α = 0 := by
  rw [← comp_powSMul, powSMul_repRestrictScalars_eq_zero, Limits.comp_zero]

/-- Reduction modulo `ℓ ^ m` of the coefficients is surjective. -/
lemma freeReduction_surjective :
    Function.Surjective (freeReduction (R := R) (G := G) ℓ m α).hom :=
  (RestrictScalars.addEquiv R _ _).symm.surjective.comp
    (Finsupp.mapRange_surjective _ (map_zero _)
      (MonoidAlgebra.map_surjective (M := G) _ Ideal.Quotient.mk_surjective))

open Classical in
/-- An auxiliary choice: for nonzero `c` in the ideal `(ℓ ^ m)`, some `d` with `d * ℓ ^ m = c`;
`0` otherwise (in particular at `c = 0`). -/
def powDiv (c : R) : R :=
  if h : c ∈ Ideal.span {((ℓ : R) ^ m)} ∧ c ≠ 0 then
    Classical.choose (Ideal.mem_span_singleton'.1 h.1)
  else 0

/-- `powDiv ℓ m 0 = 0`. -/
lemma powDiv_zero : powDiv ℓ m (0 : R) = 0 :=
  dite_eq_right fun h => h.2 rfl

/-- For `c` in the ideal `(ℓ ^ m)`, `ℓ ^ m * powDiv ℓ m c = c`. -/
lemma pow_mul_powDiv {c : R} (hc : c ∈ Ideal.span {((ℓ : R) ^ m)}) :
    (ℓ : R) ^ m * powDiv ℓ m c = c := by
  by_cases h0 : c = 0
  · rw [h0, powDiv_zero, mul_zero]
  · have h : c ∈ Ideal.span {((ℓ : R) ^ m)} ∧ c ≠ 0 := ⟨hc, h0⟩
    rw [powDiv, dite_eq_left h, mul_comm]
    exact Classical.choose_spec (Ideal.mem_span_singleton'.1 h.1)

/-- An element of `α →₀ R[G]` whose reduction modulo `ℓ ^ m` vanishes is `ℓ ^ m` times an
element: divide each coefficient by `ℓ ^ m` with `powDiv`. -/
lemma exists_pow_smul_of_freeReduction_eq_zero {x : α →₀ MonoidAlgebra R G}
    (hx : (freeReduction ℓ m α).hom x = 0) : ∃ y, ((ℓ : R) ^ m) • y = x := by
  have hx' : freeReductionAddHom ℓ m α x = 0 := hx
  have hc : ∀ a g, (x a).coeff g ∈ Ideal.span {((ℓ : R) ^ m)} := by
    intro a g
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact congrArg (fun z => (z a).coeff g) hx'
  refine ⟨Finsupp.mapRange (fun z => MonoidAlgebra.ofCoeff
    (Finsupp.mapRange (powDiv ℓ m) (powDiv_zero ℓ m) z.coeff)) ?_ x, ?_⟩
  · exact MonoidAlgebra.coeff_injective (Finsupp.mapRange_zero (hf := powDiv_zero ℓ m))
  · ext a g
    rw [Finsupp.smul_apply, MonoidAlgebra.coeff_smul_apply, Finsupp.mapRange_apply,
      MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, smul_eq_mul, pow_mul_powDiv ℓ m (hc a g)]

/-- Reduction modulo `ℓ ^ m` of the coefficients is an epimorphism in `Rep R G`. -/
instance : Epi (freeReduction (R := R) (G := G) ℓ m α) :=
  (Rep.epi_iff_surjective _).mpr (freeReduction_surjective ℓ m α)

/-- The short complex `α →₀ R[G] → α →₀ R[G] → α →₀ (R ⧸ (ℓ ^ m))[G]` formed by
multiplication by `ℓ ^ m` and reduction of coefficients. -/
abbrev freeReductionComplex : ShortComplex (Rep.{max w u v} R G) :=
  ShortComplex.mk (powSMul ℓ m (Rep.free R G α)) (freeReduction ℓ m α)
    (powSMul_comp_freeReduction ℓ m α)

/-- The short complex `freeReductionComplex ℓ m α` is exact. -/
lemma freeReductionComplex_exact : (freeReductionComplex (R := R) (G := G) ℓ m α).Exact := by
  apply ((freeReductionComplex ℓ m α).exact_map_iff_of_faithful
    (forget₂ (Rep.{max w u v} R G) (ModuleCat.{max w u v} R))).mp
  refine (ShortComplex.moduleCat_exact_iff _).mpr fun x hx => ?_
  obtain ⟨y, hy⟩ := exists_pow_smul_of_freeReduction_eq_zero ℓ m α hx
  refine ⟨y, ?_⟩
  change (powSMul ℓ m (Rep.free R G α)).hom y = x
  rw [powSMul_hom_apply]
  exact hy

/-- The cokernel of multiplication by `ℓ ^ m` on `α →₀ R[G]` is identified, through reduction
of coefficients, with the restriction of scalars of `α →₀ (R ⧸ (ℓ ^ m))[G]`. -/
def cokernelFreeIso :
    cokernel (powSMul ℓ m (Rep.free R G α)) ≅
      (repRestrictScalars.{max w u v} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G).obj
        (Rep.free (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G α) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (freeReductionComplex_exact ℓ m α).gIsCokernel

/-- The projection to the cokernel followed by `cokernelFreeIso` is reduction of coefficients. -/
@[reassoc (attr := simp)]
lemma cokernelπ_cokernelFreeIso_hom :
    cokernel.π (powSMul ℓ m (Rep.free R G α)) ≫ (cokernelFreeIso ℓ m α).hom =
      freeReduction ℓ m α :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

/-- The cokernel of multiplication by `ℓ ^ m` on `α →₀ R[G]` is `FreeOverPowQuotient ℓ m`. -/
theorem freeOverPowQuotient_cokernel_powSMul_free :
    FreeOverPowQuotient ℓ m (cokernel (powSMul ℓ m (Rep.free R G α))) :=
  freeOverPowQuotient_of_iso (cokernelFreeIso ℓ m α).symm
    (freeOverPowQuotient_repRestrictScalars _ (Representation.free_asModule_free _ G α))

variable {ℓ} in
/-- If `ℓ` is a non-zero-divisor in `R`, it is a non-zero-divisor on `α →₀ R[G]`. -/
lemma isSMulRegular_free (hℓ : IsSMulRegular R (ℓ : R)) :
    IsSMulRegular (α →₀ MonoidAlgebra R G) (ℓ : R) := by
  intro x y h
  ext a g
  exact hℓ (congrArg (fun z : α →₀ MonoidAlgebra R G => (z a).coeff g) h)

variable {ℓ} in
/-- If `ℓ` is a non-zero-divisor in `R`, multiplication by `ℓ` on `α →₀ R[G]` is a
monomorphism in `Rep R G`. -/
lemma mono_powSMul_free (hℓ : IsSMulRegular R (ℓ : R)) : Mono (powSMul ℓ 1 (Rep.free R G α)) :=
  (mono_powSMul_one_iff_isSMulRegular ℓ _).mpr (isSMulRegular_free α hℓ)

end FreeRep

section Free

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] (ℓ m : ℕ) (P : Rep.{max w u v} R G)
  [Module.Free (MonoidAlgebra R G) P.ρ.asModule]

/-- A representation that is free over `R[G]` is isomorphic to the free representation on a
chosen basis. -/
def isoFreeOfFree : P ≅ Rep.free R G (Module.Free.ChooseBasisIndex (MonoidAlgebra R G)
    P.ρ.asModule) :=
  Rep.toModuleMonoidAlgebra.preimageIso (LinearEquiv.toModuleIso
    ((Module.Free.chooseBasis (MonoidAlgebra R G) P.ρ.asModule).repr ≪≫ₗ
      Representation.finsuppLEquivFreeAsModule R G _))

/-- For `P` free over `R[G]`, the cokernel of multiplication by `ℓ ^ m` on `P` is
`FreeOverPowQuotient ℓ m`. -/
theorem freeOverPowQuotient_cokernel_powSMul_of_free :
    FreeOverPowQuotient ℓ m (cokernel (powSMul ℓ m P)) :=
  freeOverPowQuotient_of_iso
    (cokernel.mapIso (powSMul ℓ m P) (powSMul ℓ m (Rep.free R G _)) (isoFreeOfFree P)
      (isoFreeOfFree P) (comp_powSMul ℓ m (isoFreeOfFree P).hom).symm).symm
    (freeOverPowQuotient_cokernel_powSMul_free ℓ m _)

variable {ℓ} in
/-- For `P` free over `R[G]` and `ℓ` a non-zero-divisor in `R`, multiplication by `ℓ` on `P` is
a monomorphism. -/
lemma mono_powSMul_of_free (hℓ : IsSMulRegular R (ℓ : R)) : Mono (powSMul ℓ 1 P) := by
  have := mono_powSMul_free (G := G)
    (Module.Free.ChooseBasisIndex (MonoidAlgebra R G) P.ρ.asModule) hℓ
  have h : powSMul ℓ 1 P = (isoFreeOfFree P).hom ≫ powSMul ℓ 1 (Rep.free R G _) ≫
      (isoFreeOfFree P).inv := by
    rw [← comp_powSMul, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h]
  infer_instance

end Free

section ReductionSystem

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] {ℓ : ℕ} (P : Rep.{max w u v} R G)
  [Module.Free (MonoidAlgebra R G) P.ρ.asModule] [Mono (powSMul ℓ 1 P)]

/-- For `P` free over `R[G]` with multiplication by `ℓ` injective, every level `P / ℓ ^ m P` of
the reduction system of `P` is `FreeOverPowQuotient ℓ m`. -/
theorem freeOverPowQuotient_reductionSystem_obj (m : ℕ) :
    FreeOverPowQuotient ℓ m ((reductionSystem ℓ P).obj m) :=
  freeOverPowQuotient_cokernel_powSMul_of_free ℓ m P

variable (W : DivisibleSystem (Rep.{max w u v} R G) ℓ)

/-- For `P` free over `R[G]` with multiplication by `ℓ` injective, the transitions of the
inverse system `Hom(P / ℓ ^ m P, W m)` are surjective. -/
lemma homSystem_reductionSystem_map_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective ((homSystem R (reductionSystem ℓ P) W).map φ) :=
  homSystem_map_surjective_of_freeOverPowQuotient _ W
    (freeOverPowQuotient_reductionSystem_obj P) φ

/-- For `P` free over `R[G]` with multiplication by `ℓ` injective, the inverse system
`Hom(P / ℓ ^ m P, W m)` satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_homSystem_reductionSystem :
    (homSystem R (reductionSystem ℓ P) W ⋙
      CategoryTheory.forget (ModuleCat.{max w u v} R)).IsMittagLeffler :=
  isMittagLeffler_homSystem_of_freeOverPowQuotient _ W
    (freeOverPowQuotient_reductionSystem_obj P)

end ReductionSystem

end Langlands.Cohomology.DivisibleSystem
