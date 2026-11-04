import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Langlands.Cohomology.DivisibleSystem.FreeQuotientLimit
import Langlands.Cohomology.DivisibleSystem.FreeRestrictScalars
import Langlands.Cohomology.DivisibleSystem.LevelProjective

/-!
# Freeness of the terms of Harris's complexes `C_m^{•,H}` over `(R ⧸ (ℓ ^ m))[G ⧸ H]`

Harris 1999, p.306, states that "another snake lemma argument shows that `C_m^{•,H}` is an
ℓ-divisible system of complexes of free `ℤ/ℓ^mℤ[S(e)/H]`-modules as `m` varies", and Remark 2.9
that "the free `ℤ/ℓ^mℤ[S(ẽ)/H]`-complexes `C_m^{•,H}` will also be used in the calculations".
The published module `InvariantTotalProjective` proves only relative projectivity of these terms.
This module proves the freeness for the Library's `C_m^{•,H}` (the total complexes
`groupStandardTotalSystem` of the standard resolutions along `Ind_1^Γ Res_1^Γ`) whenever
`ℓ = u π ^ e` in the coefficient ring (`IsUnitMulUniformizerPow`, published module
`LevelProjective`):

* `FreeOverPowQuotientModule R ℓ m M`: `M` is isomorphic to `ι →₀ R ⧸ (ℓ ^ m)`, Harris's "free
  over `ℤ/ℓ^mℤ`" (p.304) for `R`-modules; `linearEquivFinsuppQuotient` turns a generating family
  whose relations are exactly the coefficientwise multiples of `I` into an isomorphism with
  `ι →₀ R ⧸ I`, and `DivisibleSystem.freeOverPowQuotientModule_obj` applies it to the generators
  of `exists_free_generators_obj` (LevelProjective module);
* `indBotLinearEquiv`, `indBotEquiv`: Mathlib's induction from the trivial subgroup of a
  representation on `A` is the permutation representation of `Γ` on `Γ →₀ A`, by
  `⟦γ ⊗ a⟧ ↦ single γ⁻¹ a`;
* `freeOverPowQuotient_indResBot_obj`, `freeOverPowQuotient_standardPow_indResBot_obj`:
  `Ind_1^Γ Res_1^Γ V`, and every iterate `(Ind_1^Γ Res_1^Γ)^(r+1) V`, is free over
  `(R ⧸ (ℓ ^ m))[Γ]` (`FreeOverPowQuotient`) when the underlying module of `V` is free over
  `R ⧸ (ℓ ^ m)`;
* `freeOverPowQuotient_of_isColimit`, `freeOverPowQuotient_total_X`: finite coproducts, and so
  the terms of a total complex with finitely many summands in each degree, preserve
  `FreeOverPowQuotient`;
* `TermwiseFreeOverPowQuotient T`: every term of every level `T m` of an `ℓ`-divisible system of
  `ℤ`-graded complexes of representations is free over `(R ⧸ (ℓ ^ m))[G]`; it implies
  `TermwisePowTorsionProjective`;
* `termwiseFreeOverPowQuotient_groupStandardTotalSystem` (with the hypothesis on the underlying
  modules of the terms in the rows `q < N`) and its forms `..._of_isUnitMulUniformizerPow` for
  `groupStandardTotalSystem`, `quotientInvariantsTotalSystem`,
  `smoothGodementInvariantTotalSystem` and `proPSmoothGodementInvariantTotalSystem`, without that
  hypothesis.

The route is not Harris's snake lemma argument: the terms of `C_m^{•,H}` are finite coproducts of
induced representations `Ind_1^Γ (P^r M)`, which are free over the group algebra as soon as the
underlying module of `P^r M` is free over `R ⧸ (ℓ ^ m)`; that freeness comes from the axioms of
`ℓ`-divisible systems through the LevelProjective module.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Langlands.Induction

universe w v u uR uG

section FreeModule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A family `v` whose linear combinations exhaust `M`, such that a linear combination vanishes
exactly when all its coefficients lie in `I`, identifies `M` with `ι →₀ R ⧸ I`. -/
def linearEquivFinsuppQuotient {ι : Type*} (v : ι → M) (I : Ideal R)
    (hsurj : Function.Surjective (Finsupp.linearCombination R v))
    (hker : ∀ c : ι →₀ R, Finsupp.linearCombination R v c = 0 ↔ ∀ i, c i ∈ I) :
    M ≃ₗ[R] (ι →₀ R ⧸ I) :=
  let g : (ι →₀ R) →ₗ[R] (ι →₀ R ⧸ I) := Finsupp.mapRange.linearMap I.mkQ
  have hg : Function.Surjective g :=
    Finsupp.mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective I)
  have heq : LinearMap.ker (Finsupp.linearCombination R v) = LinearMap.ker g := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hker, Finsupp.ext_iff]
    refine forall_congr' fun i => ?_
    change c i ∈ I ↔ Submodule.Quotient.mk (p := I) (c i) = 0
    rw [Submodule.Quotient.mk_eq_zero]
  ((LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
    (Submodule.quotEquivOfEq _ _ heq)).trans (LinearMap.quotKerEquivOfSurjective g hg)

variable (R) (ℓ m : ℕ) in
/-- Harris 1999, p.304, "free over `ℤ/ℓ^mℤ`", for an `R`-module: `M` is isomorphic, as an
`R`-module, to `ι →₀ R ⧸ (ℓ ^ m)` for some index type `ι`. -/
def FreeOverPowQuotientModule (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ ι : Type v, Nonempty (M ≃ₗ[R] (ι →₀ R ⧸ Ideal.span {((ℓ : R) ^ m)}))

variable {ℓ m : ℕ}

/-- `FreeOverPowQuotientModule` is invariant under linear equivalence. -/
lemma FreeOverPowQuotientModule.of_linearEquiv {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : FreeOverPowQuotientModule R ℓ m M) :
    FreeOverPowQuotientModule R ℓ m N := by
  obtain ⟨ι, ⟨f⟩⟩ := hM
  exact ⟨ι, ⟨e.symm.trans f⟩⟩

namespace DivisibleSystem

variable {π : R} {e : ℕ}

/-- Harris 1999, p.304, "`T_m` is free over `ℤ/ℓ^mℤ`", for an `ℓ`-divisible system of
`R`-modules when `ℓ = u π ^ e` (`IsUnitMulUniformizerPow`): the level `T m` is isomorphic to
`ι →₀ R ⧸ (ℓ ^ m)`. -/
theorem freeOverPowQuotientModule_obj (h : IsUnitMulUniformizerPow ℓ π e)
    (T : DivisibleSystem (ModuleCat.{v} R) ℓ) (m : ℕ) :
    FreeOverPowQuotientModule R ℓ m (T.obj m) := by
  obtain ⟨ι, v, hsurj, hker⟩ := T.exists_free_generators_obj h m
  exact ⟨ι, ⟨linearEquivFinsuppQuotient v _ hsurj fun c =>
    (hker c).trans (forall_congr' fun i => Ideal.mem_span_singleton.symm)⟩⟩

end DivisibleSystem

end FreeModule

section IndBot

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ]

/-- The coinvariants of a representation of the trivial subgroup are the whole module: the
submodule spanned by the `τ g x - x` is zero. -/
lemma coinvariantsKer_bot_eq_bot {V : Type*} [AddCommGroup V] [Module k V]
    (τ : Representation k (⊥ : Subgroup Γ) V) : Representation.Coinvariants.ker τ = ⊥ := by
  rw [Representation.Coinvariants.ker, Submodule.span_eq_bot]
  rintro _ ⟨⟨g, x⟩, rfl⟩
  show τ g x - x = 0
  rw [Subsingleton.elim g 1, map_one, Module.End.one_apply, sub_self]

variable {A : Type*} [AddCommGroup A] [Module k A]

open scoped Classical in
/-- Mathlib's induction from the trivial subgroup, `(k[Γ] ⊗_k A)_⊥`, is `Γ →₀ A`, by
`⟦γ ⊗ a⟧ ↦ single γ⁻¹ a`. -/
def indBotLinearEquiv (ρ : Representation k (⊥ : Subgroup Γ) A) :
    Representation.IndV (⊥ : Subgroup Γ).subtype ρ ≃ₗ[k] (Γ →₀ A) :=
  (Submodule.quotEquivOfEqBot _ (coinvariantsKer_bot_eq_bot _)).trans <|
    (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k) (LinearEquiv.refl k A)).trans <|
      (TensorProduct.finsuppScalarLeft k A Γ).trans (Finsupp.domLCongr (Equiv.inv Γ))

open scoped Classical in
lemma indBotLinearEquiv_mk (ρ : Representation k (⊥ : Subgroup Γ) A) (γ : Γ) (a : A) :
    indBotLinearEquiv ρ (Representation.IndV.mk _ ρ γ a) = Finsupp.single γ⁻¹ a := by
  change Finsupp.domLCongr (R := k) (Equiv.inv Γ) (TensorProduct.finsuppScalarLeft k A Γ
    (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k) (LinearEquiv.refl k A)
      (MonoidAlgebra.single γ (1 : k) ⊗ₜ[k] a))) = _
  rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, TensorProduct.finsuppScalarLeft_apply_tmul,
    Finsupp.sum_single_index (by simp), one_smul, Finsupp.domLCongr_single, Equiv.inv_apply]

/-- Mathlib's induction from the trivial subgroup is the permutation representation of `Γ` on
`Γ →₀ A` by left multiplication. -/
def indBotEquiv (ρ : Representation k (⊥ : Subgroup Γ) A) :
    (ρ.ind (⊥ : Subgroup Γ).subtype).Equiv (permutation k Γ Γ A) :=
  .mk (indBotLinearEquiv ρ) fun h => Representation.IndV.hom_ext _ _ fun γ => LinearMap.ext fun a => by
    change indBotLinearEquiv ρ (ρ.ind _ h (Representation.IndV.mk _ ρ γ a)) =
      permutation k Γ Γ A h (indBotLinearEquiv ρ (Representation.IndV.mk _ ρ γ a))
    rw [Representation.ind_mk, indBotLinearEquiv_mk, indBotLinearEquiv_mk, permutation_single,
      mul_inv_rev, inv_inv, smul_eq_mul]

end IndBot

namespace DivisibleSystem

section IndResBot

variable (k : Type u) [CommRing k] {Γ : Type v} [Group Γ] {ℓ m : ℕ}

/-- `Ind_1^Γ Res_1^Γ V` is free over `(R ⧸ (ℓ ^ m))[Γ]` when the underlying module of `V` is free
over `R ⧸ (ℓ ^ m)`. -/
theorem freeOverPowQuotient_indResBot_obj {V : Rep.{max w u v} k Γ}
    (hV : FreeOverPowQuotientModule k ℓ m V) :
    FreeOverPowQuotient ℓ m ((indResBot.{w} k Γ).obj V) := by
  obtain ⟨ι, ⟨e⟩⟩ := hV
  exact freeOverPowQuotient_of_equiv_permutation _
    ((indBotEquiv _).trans (permutationCongr k Γ Γ e))

/-- The underlying module of `Ind_1^Γ Res_1^Γ V` is free over `R ⧸ (ℓ ^ m)` when that of `V` is:
it is `Γ →₀ V`. -/
theorem freeOverPowQuotientModule_indResBot_obj {V : Rep.{max w u v} k Γ}
    (hV : FreeOverPowQuotientModule k ℓ m V) :
    FreeOverPowQuotientModule k ℓ m ((indResBot.{w} k Γ).obj V) := by
  obtain ⟨ι, ⟨e⟩⟩ := hV
  exact ⟨Γ × ι, ⟨(indBotLinearEquiv _).trans
    ((Finsupp.mapRange.linearEquiv e).trans (Finsupp.curryLinearEquiv k).symm)⟩⟩

/-- The underlying modules of the iterates `P^r V` of `P = Ind_1^Γ Res_1^Γ` are free over
`R ⧸ (ℓ ^ m)` when that of `V` is. -/
theorem freeOverPowQuotientModule_standardPow_indResBot_obj {V : Rep.{max w u v} k Γ}
    (hV : FreeOverPowQuotientModule k ℓ m V) :
    ∀ r : ℕ, FreeOverPowQuotientModule k ℓ m ((standardPow (indResBot.{w} k Γ) r).obj V)
  | 0 => hV
  | r + 1 => freeOverPowQuotientModule_indResBot_obj k
      (freeOverPowQuotientModule_standardPow_indResBot_obj hV r)

/-- The iterates `P^(r+1) V` of `P = Ind_1^Γ Res_1^Γ` are free over `(R ⧸ (ℓ ^ m))[Γ]` when the
underlying module of `V` is free over `R ⧸ (ℓ ^ m)`. -/
theorem freeOverPowQuotient_standardPow_indResBot_obj {V : Rep.{max w u v} k Γ}
    (hV : FreeOverPowQuotientModule k ℓ m V) (r : ℕ) :
    FreeOverPowQuotient ℓ m ((standardPow (indResBot.{w} k Γ) (r + 1)).obj V) :=
  freeOverPowQuotient_indResBot_obj k (freeOverPowQuotientModule_standardPow_indResBot_obj k hV r)

end IndResBot

section Coproduct

variable {G : Type v} [Monoid G]

instance toModuleMonoidAlgebra_additive {S : Type u} [CommRing S] :
    (Rep.toModuleMonoidAlgebra.{w} (k := S) (G := G)).Additive where
  map_add := rfl

/-- A finite coproduct of representations that are free over the group algebra is free over the
group algebra. -/
theorem free_asModule_sigma {S : Type u} [CommRing S] {J : Type} [Finite J]
    (Y : J → Rep.{w} S G) [HasCoproduct Y]
    (hY : ∀ j, Module.Free (MonoidAlgebra S G) (Y j).ρ.asModule) :
    Module.Free (MonoidAlgebra S G) (∐ Y).ρ.asModule := by
  classical
  let F := Rep.toModuleMonoidAlgebra.{w} (k := S) (G := G)
  let e : F.obj (∐ Y) ≅ ModuleCat.of _ (DirectSum J fun j => F.obj (Y j)) :=
    PreservesCoproduct.iso F Y ≪≫ ModuleCat.coprodIsoDirectSum (fun j => F.obj (Y j))
  have : ∀ j, Module.Free (MonoidAlgebra S G) (F.obj (Y j)) := hY
  exact Module.Free.of_equiv (e.toLinearEquiv.symm :
    (DirectSum J fun j => F.obj (Y j)) ≃ₗ[MonoidAlgebra S G] F.obj (∐ Y))

variable {R : Type u} [CommRing R] {ℓ m : ℕ}

/-- The point of a colimit cofan of finitely many representations free over
`(R ⧸ (ℓ ^ m))[G]` is free over `(R ⧸ (ℓ ^ m))[G]`. -/
theorem freeOverPowQuotient_of_isColimit {J : Type} [Finite J] {f : J → Rep.{w} R G}
    (c : Cofan f) (hc : IsColimit c) (hf : ∀ j, FreeOverPowQuotient ℓ m (f j)) :
    FreeOverPowQuotient ℓ m c.pt := by
  classical
  choose Y hY e using fun j => (freeOverPowQuotient_iff (f j)).1 (hf j)
  let F := repRestrictScalars.{w} R (R ⧸ Ideal.span {((ℓ : R) ^ m)}) G
  refine (freeOverPowQuotient_iff c.pt).2 ⟨∐ Y, free_asModule_sigma Y hY, ⟨?_⟩⟩
  exact PreservesCoproduct.iso F Y ≪≫ Sigma.mapIso (fun j => (e j).some) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso hc

/-- The terms of the total complex of a double complex of representations are free over
`(R ⧸ (ℓ ^ m))[G]` when the summands are and each total degree has finitely many summands. -/
theorem freeOverPowQuotient_total_X {I₁ I₂ I₁₂ : Type} {c₁ : ComplexShape I₁}
    {c₂ : ComplexShape I₂} (K : HomologicalComplex₂ (Rep.{w} R G) c₁ c₂)
    (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂] [K.HasTotal c₁₂]
    (i₁₂ : I₁₂)
    [Finite (ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {i₁₂})]
    (hK : ∀ i₁ i₂, ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂ →
      FreeOverPowQuotient ℓ m ((K.X i₁).X i₂)) :
    FreeOverPowQuotient ℓ m ((K.total c₁₂).X i₁₂) :=
  freeOverPowQuotient_of_isColimit _ (K.toGradedObject.isColimitCofanMapObj _ i₁₂)
    fun i => hK i.1.1 i.1.2 i.2

end Coproduct

section Termwise

variable {R : Type u} [CommRing R] {G : Type v} [Monoid G] {ℓ : ℕ}

/-- Harris 1999, p.306 and Remark 2.9, "complexes of free `ℤ/ℓ^mℤ[S(e)/H]`-modules", for an
`ℓ`-divisible system of `ℤ`-graded cochain complexes of representations of `G` (standing for
`S(e)/H`): every term of every level `T m` is free over `(R ⧸ (ℓ ^ m))[G]`
(`FreeOverPowQuotient`). -/
def TermwiseFreeOverPowQuotient (T : DivisibleSystem (CochainComplex (Rep.{w} R G) ℤ) ℓ) :
    Prop :=
  ∀ m p, FreeOverPowQuotient ℓ m ((T.obj m).X p)

/-- Termwise freeness over `(R ⧸ (ℓ ^ m))[G]` implies `TermwisePowTorsionProjective`. -/
lemma TermwiseFreeOverPowQuotient.termwisePowTorsionProjective
    {T : DivisibleSystem (CochainComplex (Rep.{w} R G) ℤ) ℓ}
    (hT : TermwiseFreeOverPowQuotient T) : TermwisePowTorsionProjective T :=
  fun m p => powTorsionProjective_of_freeOverPowQuotient (hT m p)

end Termwise

section GroupTotal

variable (k : Type u) [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ} (N : ℕ)
  (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ)

/-- The total complexes, rows `q < N`, of the standard resolutions along `Ind_1^Γ Res_1^Γ` of an
`ℓ`-divisible system of complexes of representations of a finite group `Γ` are termwise free over
`(R ⧸ (ℓ ^ m))[Γ]` when the underlying module of every level-`m` term in degree `q < N` is free
over `R ⧸ (ℓ ^ m)`. -/
theorem termwiseFreeOverPowQuotient_groupStandardTotalSystem
    (hK : ∀ m, ∀ q < N, FreeOverPowQuotientModule k ℓ m ((K.obj m).X q)) :
    TermwiseFreeOverPowQuotient (groupStandardTotalSystem.{w} N K) :=
  fun m n => freeOverPowQuotient_total_X
    (((upFinEmbedding N).restrictionFunctor _).obj
      ((K.standardResolutionDoubleComplexes (indResBot.{w} k Γ) (indResBotCounit k Γ)).obj m))
    (ComplexShape.up ℤ) n
    (fun q r _ => freeOverPowQuotient_standardPow_indResBot_obj k (hK m q q.2) r)

variable {π : k} {e : ℕ}

/-- If `ℓ = u π ^ e` in `k` (`IsUnitMulUniformizerPow`), the total complexes, rows `q < N`, of
the standard resolutions along `Ind_1^Γ Res_1^Γ` of an `ℓ`-divisible system of complexes of
representations of a finite group `Γ` are termwise free over `(k ⧸ (ℓ ^ m))[Γ]`. -/
theorem termwiseFreeOverPowQuotient_groupStandardTotalSystem_of_isUnitMulUniformizerPow
    (hℓ : IsUnitMulUniformizerPow ℓ π e) :
    TermwiseFreeOverPowQuotient (groupStandardTotalSystem.{w} N K) :=
  termwiseFreeOverPowQuotient_groupStandardTotalSystem k N K fun m q _ =>
    ((K.degree q).map (forget₂ (Rep.{max w u v} k Γ) (ModuleCat.{max w u v} k))
      ).freeOverPowQuotientModule_obj hℓ m

end GroupTotal

section SmoothTotal

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  {π : R} {e : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))

/-- Harris 1999, p.306 and Remark 2.9, when `ℓ = u π ^ e` in `R` (`IsUnitMulUniformizerPow`):
the terms of Harris's `C_m^{•,H}` (`quotientInvariantsTotalSystem`) are free over
`(R ⧸ (ℓ ^ m))[G/H]`. -/
theorem termwiseFreeOverPowQuotient_quotientInvariantsTotalSystem_of_isUnitMulUniformizerPow
    (hℓ : IsUnitMulUniformizerPow ℓ π e) :
    TermwiseFreeOverPowQuotient (K.quotientInvariantsTotalSystem N H hK) :=
  termwiseFreeOverPowQuotient_groupStandardTotalSystem_of_isUnitMulUniformizerPow.{w, uG, uR} R
    N (K.quotientInvariantsComplexes H hK) hℓ

end SmoothTotal

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ} {π : R} {e : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- Harris 1999, p.306 and Remark 2.9, when `ℓ = u π ^ e` in `R` (`IsUnitMulUniformizerPow`):
the terms of Harris's `C_m^{•,H}` for the truncated smooth Godement resolutions
(`smoothGodementInvariantTotalSystem`) are free over `(R ⧸ (ℓ ^ m))[G/H]`. -/
theorem
    termwiseFreeOverPowQuotient_smoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow
    (hℓ : IsUnitMulUniformizerPow ℓ π e) :
    TermwiseFreeOverPowQuotient (smoothGodementInvariantTotalSystem h T D H hterm hres) :=
  termwiseFreeOverPowQuotient_groupStandardTotalSystem_of_isUnitMulUniformizerPow.{0} R (D + 2)
    _ hℓ

end SmoothGodement

section ProPSmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ} {π : R} {e : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (hP : ProPInvariantsExactStatement.{u, u, u}) {p : ℕ} {H : Subgroup G} [H.Normal]
  [H.FiniteIndex] (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- Harris 1999, p.306 and Remark 2.9, when `ℓ = u π ^ e` in `R` (`IsUnitMulUniformizerPow`):
the terms of Harris's `C_m^{•,H}` for the truncated smooth Godement resolutions and a normal
pro-`p` subgroup `H` of finite index (`proPSmoothGodementInvariantTotalSystem`) are free over
`(R ⧸ (ℓ ^ m))[G/H]`. -/
theorem
    termwiseFreeOverPowQuotient_proPSmoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow
    (hℓ : IsUnitMulUniformizerPow ℓ π e) :
    TermwiseFreeOverPowQuotient
      (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres) :=
  termwiseFreeOverPowQuotient_groupStandardTotalSystem_of_isUnitMulUniformizerPow.{0} R (D + 2)
    _ hℓ

end ProPSmoothGodement

end DivisibleSystem

end Langlands.Cohomology
