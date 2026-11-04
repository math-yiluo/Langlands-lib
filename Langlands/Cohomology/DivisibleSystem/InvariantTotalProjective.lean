import Langlands.Cohomology.DivisibleSystem.FreeTorsionProjective
import Langlands.Cohomology.DivisibleSystem.ProPInvariants

/-!
# Relative projectivity of the terms of Harris's complexes `C_m^{•,H}`

Harris 1999, p.306, states that `C_m^{•,H}` "is an ℓ-divisible system of complexes of free
`ℤ/ℓ^mℤ[S(e)/H]`-modules", and Remark 2.9 that "the free `ℤ/ℓ^mℤ[S(ẽ)/H]`-complexes
`C_m^{•,H}` will also be used in the calculations". In the proof of Proposition 4.10 (p.312) he
writes `T_m(j,ẽ) = Hom_{𝒪/ℓ^m𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))` and deduces
the surjectivity of the maps (4.10.3) `T_{m+1}(j,ẽ) → T_m(j,ẽ)` from the freeness of both
arguments over `𝒪/ℓ^m𝒪[S(ẽ)/H_p]`.

The published module `HomSurjective` replaces that freeness by the hypothesis
`PowTorsionProjective ℓ m` on the source. This module proves that hypothesis for the terms of
the total complexes `groupStandardTotalSystem` (and hence for the Library's `C_m^{•,H}`), given
that the underlying modules of the terms of the system being resolved satisfy it:

* `powTorsionProjective_total_X`: the terms of a total complex inherit the property from the
  terms of the double complex; `termwisePowTorsionProjective_totalSystem` and
  `termwisePowTorsionProjective_standardTotalSystem` for the systems of the Total module, with
  hypotheses only on the rows `q < N`;
* `powTorsionProjective_indFunctor_obj`, `powTorsionProjective_resFunctor_obj`: induction from a
  subgroup and restriction to a subgroup of finite index preserve the property (Mathlib's
  adjunctions `Rep.indResAdjunction` and `Rep.resIndAdjunction`);
* `powTorsionProjective_iff_forget₂_of_subsingleton`: for a monoid with at most one element the
  property of a representation is that of its underlying module;
  `powTorsionProjective_forget₂_obj_of_freeOverPowQuotient` derives the hypothesis on the
  underlying module from the freeness of the restriction to the trivial subgroup over
  `(R ⧸ (ℓ ^ m))[⊥]`, a form of Harris's requirement (p.304) that the members of an
  `ℓ`-divisible system be free over `ℤ/ℓ^mℤ`;
* `powTorsionProjective_standardPow_indResBot_obj`: for a finite group `Γ`, every iterate
  `(Ind_1^Γ Res_1^Γ)^(r+1) X` has the property when the underlying module of `X` has it;
* `UnderlyingPowTorsionProjectiveBelow N K`: the underlying modules of the level-`m` terms of
  `K` in the degrees `q < N` have the property, for every `m`; it follows from
  `FreeOverPowQuotient` of the restrictions of these terms to the trivial subgroup
  (`underlyingPowTorsionProjectiveBelow_of_freeOverPowQuotient`);
* for `groupStandardTotalSystem` and its specializations `quotientInvariantsTotalSystem`,
  `smoothGodementInvariantTotalSystem` and `proPSmoothGodementInvariantTotalSystem`:
  `TermwisePowTorsionProjective`, the surjectivity of the transitions of the inverse system
  `T_m(j) = Hom(C_m^j, W_m)` for an `ℓ`-divisible system `W` of representations of `G ⧸ H`
  (Harris's (4.10.3)), its Mittag-Leffler condition, and the Mittag-Leffler condition of the
  Hom complexes `Hom^•(C_m^•, W_m)`.

The route differs from Harris's: only the source `C_m^j` needs the property, and the target
`W` is any `ℓ`-divisible system (epimorphic transitions, `W_m` killed by `ℓ ^ m`); Harris's
target `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` is not constructed. Freeness of the terms over
`(R ⧸ (ℓ ^ m))[G ⧸ H]` is not proved, and the hypothesis on the underlying modules of the
`H`-invariant terms stays explicit: Harris's `ℓ`-divisible systems are free over `ℤ/ℓ^mℤ`
(p.304), and he asserts the freeness of `C_m^{•,H}` after "another snake lemma argument"
(p.306) without spelling out this step.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe w v u uR uG

namespace DivisibleSystem

section TotalTerm

variable {C : Type u} [Category.{v} C] [Preadditive C] {ℓ m : ℕ}
  {I₁ I₂ I₁₂ : Type*} [DecidableEq I₁₂] {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- The terms of the total complex of a double complex whose terms are projective relative to
objects killed by `ℓ ^ m` are projective relative to objects killed by `ℓ ^ m`: the lifts of the
restrictions to the summands are assembled by `totalDesc`. -/
lemma powTorsionProjective_total_X (K : HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [K.HasTotal c₁₂]
    (hK : ∀ i₁ i₂, PowTorsionProjective ℓ m ((K.X i₁).X i₂)) (i₁₂ : I₁₂) :
    PowTorsionProjective ℓ m ((K.total c₁₂).X i₁₂) := by
  intro X Y p hp hX g
  choose f hf using fun i₁ i₂ (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) =>
    hK i₁ i₂ p hp hX (K.ιTotal c₁₂ i₁ i₂ i₁₂ h ≫ g)
  refine ⟨K.totalDesc f, HomologicalComplex₂.total.hom_ext c₁₂ fun i₁ i₂ h => ?_⟩
  rw [HomologicalComplex₂.ι_totalDesc_assoc, hf]

end TotalTerm

section Total

variable {A : Type u} [Category.{v} A] [Abelian A] {ℓ : ℕ}

/-- The terms of the total complex, rows restricted to `q < N`, of a double complex whose terms
in the rows `q < N` are projective relative to objects killed by `ℓ ^ m`. -/
lemma powTorsionProjective_upFinTotalFunctor_obj_X (N : ℕ) {m : ℕ}
    (K : HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ))
    (hK : ∀ q < N, ∀ r, PowTorsionProjective ℓ m ((K.X q).X r)) (n : ℤ) :
    PowTorsionProjective ℓ m (((upFinTotalFunctor A N).obj K).X n) :=
  powTorsionProjective_total_X (((upFinEmbedding N).restrictionFunctor _).obj K)
    (ComplexShape.up ℤ) (fun q r => hK q q.2 r) n

/-- The total complexes, rows `q < N`, of an `ℓ`-divisible system of double complexes whose
level-`m` terms in the rows `q < N` are projective relative to objects killed by `ℓ ^ m` satisfy
`TermwisePowTorsionProjective`. -/
lemma termwisePowTorsionProjective_totalSystem (N : ℕ)
    (K : DivisibleSystem (HomologicalComplex₂ A (ComplexShape.up ℕ) (ComplexShape.down ℕ)) ℓ)
    (hK : ∀ m, ∀ q < N, ∀ r, PowTorsionProjective ℓ m (((K.obj m).X q).X r)) :
    TermwisePowTorsionProjective (K.totalSystem N) :=
  fun m n => powTorsionProjective_upFinTotalFunctor_obj_X N (K.obj m) (hK m) n

/-- The total complexes of the standard resolutions along `P` of an `ℓ`-divisible system of
`ℕ`-graded cochain complexes (rows `q < N`) satisfy `TermwisePowTorsionProjective` when every
`P^(r+1)` of every level-`m` term in degree `q < N` is projective relative to objects killed by
`ℓ ^ m`. -/
lemma termwisePowTorsionProjective_standardTotalSystem (N : ℕ) (P : A ⥤ A) (ε : P ⟶ 𝟭 A)
    [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (K : DivisibleSystem (CochainComplex A ℕ) ℓ)
    (hK : ∀ m, ∀ q < N, ∀ r,
      PowTorsionProjective ℓ m ((standardPow P (r + 1)).obj ((K.obj m).X q))) :
    TermwisePowTorsionProjective (K.standardTotalSystem N P ε) :=
  termwisePowTorsionProjective_totalSystem N _ hK

end Total

section Group

variable (k : Type u) [CommRing k] {Γ : Type v} [Group Γ] {ℓ m : ℕ}

/-- Induction `Ind_S^Γ` from a subgroup preserves projectivity relative to objects killed by
`ℓ ^ m`: it is left adjoint to restriction (Mathlib's `Rep.indResAdjunction`), which is additive
and preserves epimorphisms. -/
lemma powTorsionProjective_indFunctor_obj (S : Subgroup Γ) {Y : Rep.{max w u v} k S}
    (hY : PowTorsionProjective ℓ m Y) :
    PowTorsionProjective ℓ m ((Rep.indFunctor.{max w u v} k S.subtype).obj Y) :=
  powTorsionProjective_obj_of_adjunction (Rep.indResAdjunction.{max w u v} k S.subtype) hY

/-- Restriction `Res_S^Γ` to a subgroup of finite index preserves projectivity relative to
objects killed by `ℓ ^ m`: it is left adjoint to induction (Mathlib's `Rep.resIndAdjunction`),
which is additive (a right adjoint) and preserves epimorphisms (a left adjoint). -/
lemma powTorsionProjective_resFunctor_obj (S : Subgroup Γ) [S.FiniteIndex]
    {X : Rep.{max w u v} k Γ} (hX : PowTorsionProjective ℓ m X) :
    PowTorsionProjective ℓ m ((Rep.resFunctor.{max w u v} S.subtype).obj X) := by
  classical
  have : (Rep.indFunctor.{max w u v} k S.subtype).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact powTorsionProjective_obj_of_adjunction (Rep.resIndAdjunction.{w, u, v} k S) hX

section Subsingleton

variable {k : Type u} [CommRing k] {S : Type v} [Monoid S] [Subsingleton S] {ℓ m : ℕ}

/-- A representation of a monoid with at most one element is projective relative to objects
killed by `ℓ ^ m` if and only if its underlying module is: every linear map between the
underlying modules of representations of such a monoid is equivariant, since the monoid acts
through its unit. -/
lemma powTorsionProjective_iff_forget₂_of_subsingleton (Y : Rep.{w} k S) :
    PowTorsionProjective ℓ m Y ↔
      PowTorsionProjective ℓ m ((forget₂ (Rep.{w} k S) (ModuleCat.{w} k)).obj Y) := by
  constructor
  · intro hY A B p hp hA g
    let p' := (Rep.trivialFunctor.{w} k S).map p
    have hp' : Epi p' := (Rep.epi_iff_surjective p').2 ((ModuleCat.epi_iff_surjective p).1 hp)
    have hA' : powSMul ℓ m ((Rep.trivialFunctor.{w} k S).obj A) = 0 :=
      (forget₂ (Rep.{w} k S) (ModuleCat.{w} k)).map_injective
        (by rw [map_powSMul, Functor.map_zero]; exact hA)
    let g' : Y ⟶ (Rep.trivialFunctor.{w} k S).obj B :=
      ConcreteCategory.ofHom (C := Rep.{w} k S) ⟨g.hom, fun s => by
        rw [Subsingleton.elim s 1, map_one, map_one]
        exact LinearMap.ext fun _ => rfl⟩
    obtain ⟨f', hf'⟩ := hY p' hp' hA' g'
    refine ⟨ModuleCat.ofHom f'.hom.toLinearMap, ?_⟩
    ext y
    exact congrArg (fun φ => φ.hom y) hf'
  · intro hY X Z p hp hX g
    have hp' : Epi ((forget₂ (Rep.{w} k S) (ModuleCat.{w} k)).map p) :=
      (ModuleCat.epi_iff_surjective _).2 ((Rep.epi_iff_surjective p).1 hp)
    obtain ⟨f, hf⟩ := hY _ hp' (by rw [← map_powSMul, hX, Functor.map_zero])
      ((forget₂ (Rep.{w} k S) (ModuleCat.{w} k)).map g)
    let f' : Y ⟶ X := ConcreteCategory.ofHom (C := Rep.{w} k S) ⟨f.hom, fun s => by
      rw [Subsingleton.elim s 1, map_one, map_one]
      exact LinearMap.ext fun _ => rfl⟩
    refine ⟨f', (forget₂ (Rep.{w} k S) (ModuleCat.{w} k)).map_injective ?_⟩
    rw [Functor.map_comp]
    exact hf

end Subsingleton

section Bot

variable (k : Type u) [CommRing k] {Γ : Type v} [Group Γ] {ℓ m : ℕ}

/-- The restriction of a representation to the trivial subgroup is projective relative to
objects killed by `ℓ ^ m` if and only if its underlying module is. -/
lemma powTorsionProjective_resFunctor_bot_obj_iff (X : Rep.{max w u v} k Γ) :
    PowTorsionProjective ℓ m ((Rep.resFunctor.{max w u v} (⊥ : Subgroup Γ).subtype).obj X) ↔
      PowTorsionProjective ℓ m
        ((forget₂ (Rep.{max w u v} k Γ) (ModuleCat.{max w u v} k)).obj X) :=
  powTorsionProjective_iff_forget₂_of_subsingleton _

/-- `Ind_1^Γ Res_1^Γ X` is projective relative to objects killed by `ℓ ^ m` when the underlying
module of `X` is. -/
lemma powTorsionProjective_indResBot_obj {X : Rep.{max w u v} k Γ}
    (hX : PowTorsionProjective ℓ m
      ((forget₂ (Rep.{max w u v} k Γ) (ModuleCat.{max w u v} k)).obj X)) :
    PowTorsionProjective ℓ m ((indResBot.{w} k Γ).obj X) :=
  powTorsionProjective_indFunctor_obj k ⊥ ((powTorsionProjective_resFunctor_bot_obj_iff k X).2 hX)

/-- The underlying module of a representation is projective relative to objects killed by
`ℓ ^ m` when its restriction to the trivial subgroup is killed by `ℓ ^ m` and free over the group
algebra `(R ⧸ (ℓ ^ m))[⊥]` (`FreeOverPowQuotient`). That group algebra is `R ⧸ (ℓ ^ m)` up to
isomorphism, so this is freeness of the underlying module over `R ⧸ (ℓ ^ m)`; the
identification is not formalized. -/
lemma powTorsionProjective_forget₂_obj_of_freeOverPowQuotient {X : Rep.{max w u v} k Γ}
    (hX : FreeOverPowQuotient ℓ m
      ((Rep.resFunctor.{max w u v} (⊥ : Subgroup Γ).subtype).obj X)) :
    PowTorsionProjective ℓ m
      ((forget₂ (Rep.{max w u v} k Γ) (ModuleCat.{max w u v} k)).obj X) :=
  (powTorsionProjective_resFunctor_bot_obj_iff k X).1
    (powTorsionProjective_of_freeOverPowQuotient hX)

variable [Finite Γ]

/-- The underlying module of a representation of a finite group projective relative to objects
killed by `ℓ ^ m` is projective relative to objects killed by `ℓ ^ m`: restriction to the
trivial subgroup, which has finite index, preserves the property. -/
lemma powTorsionProjective_forget₂_obj {X : Rep.{max w u v} k Γ}
    (hX : PowTorsionProjective ℓ m X) :
    PowTorsionProjective ℓ m
      ((forget₂ (Rep.{max w u v} k Γ) (ModuleCat.{max w u v} k)).obj X) :=
  (powTorsionProjective_resFunctor_bot_obj_iff k X).1 (powTorsionProjective_resFunctor_obj k ⊥ hX)

/-- The iterates `P^(r+1) X` of `P = Ind_1^Γ Res_1^Γ`, `Γ` finite, are projective relative to
objects killed by `ℓ ^ m` when the underlying module of `X` is: `P^(r+2) X = P (P^(r+1) X)`,
and the underlying module of `P^(r+1) X` inherits the property by
`powTorsionProjective_forget₂_obj`. -/
lemma powTorsionProjective_standardPow_indResBot_obj {X : Rep.{max w u v} k Γ}
    (hX : PowTorsionProjective ℓ m
      ((forget₂ (Rep.{max w u v} k Γ) (ModuleCat.{max w u v} k)).obj X)) :
    ∀ r : ℕ, PowTorsionProjective ℓ m ((standardPow (indResBot.{w} k Γ) (r + 1)).obj X)
  | 0 => powTorsionProjective_indResBot_obj k hX
  | r + 1 => powTorsionProjective_indResBot_obj k
      (powTorsionProjective_forget₂_obj k (powTorsionProjective_standardPow_indResBot_obj hX r))

end Bot

end Group

section UnderlyingBelow

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] {ℓ : ℕ}

/-- For every `m`, the underlying modules of the level-`m` terms in the degrees `q < N` of an
`ℓ`-divisible system of `ℕ`-graded cochain complexes of representations are projective relative
to objects killed by `ℓ ^ m`. For a finite group this is the hypothesis under which the total
complexes of the standard resolutions along `Ind_1^Γ Res_1^Γ`, rows `q < N`, satisfy
`TermwisePowTorsionProjective`. -/
def UnderlyingPowTorsionProjectiveBelow (N : ℕ)
    (K : DivisibleSystem (CochainComplex (Rep.{w} k Γ) ℕ) ℓ) : Prop :=
  ∀ m, ∀ q < N, PowTorsionProjective ℓ m
    ((forget₂ (Rep.{w} k Γ) (ModuleCat.{w} k)).obj ((K.obj m).X q))

/-- `UnderlyingPowTorsionProjectiveBelow` holds when the restrictions to the trivial subgroup of
the level-`m` terms in the degrees `q < N` are free over `(R ⧸ (ℓ ^ m))[⊥]`
(`FreeOverPowQuotient`). -/
lemma underlyingPowTorsionProjectiveBelow_of_freeOverPowQuotient (N : ℕ)
    (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ)
    (hK : ∀ m, ∀ q < N, FreeOverPowQuotient ℓ m
      ((Rep.resFunctor.{max w u v} (⊥ : Subgroup Γ).subtype).obj ((K.obj m).X q))) :
    UnderlyingPowTorsionProjectiveBelow N K :=
  fun m q hq => powTorsionProjective_forget₂_obj_of_freeOverPowQuotient k (hK m q hq)

end UnderlyingBelow

section GroupTotal

variable (k : Type u) [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ} (N : ℕ)
  (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ)
  (hK : UnderlyingPowTorsionProjectiveBelow N K)

include hK

/-- The total complexes of the standard resolutions along `Ind_1^Γ Res_1^Γ` of an `ℓ`-divisible
system of complexes of representations of a finite group `Γ` satisfy
`TermwisePowTorsionProjective` when the underlying module of every level-`m` term in degree
`q < N` is projective relative to objects killed by `ℓ ^ m`. -/
lemma termwisePowTorsionProjective_groupStandardTotalSystem :
    TermwisePowTorsionProjective (groupStandardTotalSystem.{w} N K) :=
  termwisePowTorsionProjective_standardTotalSystem N _ _ K fun m q hq r =>
    powTorsionProjective_standardPow_indResBot_obj k (hK m q hq) r

variable (W : DivisibleSystem (Rep.{max w u v} k Γ) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^j, W_m)` with `C_m^•` the total
complexes `groupStandardTotalSystem`: the transitions of the inverse system of the `T_m(j)`
are surjective. -/
lemma groupStandardTotalSystem_degree_homSystem_map_surjective (j : ℤ) {m m' : ℕᵒᵖ}
    (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem k ((groupStandardTotalSystem.{w} N K).degree j) W).map φ) :=
  homSystem_map_surjective k _ W
    (fun m => termwisePowTorsionProjective_groupStandardTotalSystem k N K hK m j) φ

/-- The inverse system of the `T_m(j) = Hom(C_m^j, W_m)`, `C_m^•` the total complexes
`groupStandardTotalSystem`, satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_groupStandardTotalSystem_degree_homSystem (j : ℤ) :
    (homSystem k ((groupStandardTotalSystem.{w} N K).degree j) W ⋙
      CategoryTheory.forget (ModuleCat.{max w u v} k)).IsMittagLeffler :=
  isMittagLeffler_homSystem k _ W
    fun m => termwisePowTorsionProjective_groupStandardTotalSystem k N K hK m j

/-- Every morphism `C_n^j ⟶ W_n`, `C_n^•` the total complexes `groupStandardTotalSystem`, is the
level-`n` component of a morphism of inverse systems. -/
lemma groupStandardTotalSystem_degree_towerHomEval_surjective (j : ℤ) (n : ℕ) :
    Function.Surjective
      (towerHomEval k ((groupStandardTotalSystem.{w} N K).degree j) W n) :=
  towerHomEval_surjective k _ W
    (fun m => termwisePowTorsionProjective_groupStandardTotalSystem k N K hK m j) n

variable (W : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℤ) ℓ)

/-- The degree-`n` components of the transitions of the Hom complexes `Hom^•(C_m^•, W_m)`,
`C_m^•` the total complexes `groupStandardTotalSystem`, are surjective. -/
lemma groupStandardTotalSystem_homComplexSystem_map_f_surjective {m m' : ℕᵒᵖ} (φ : m ⟶ m')
    (n : ℤ) :
    Function.Surjective
      (((homComplexSystem k (groupStandardTotalSystem.{w} N K) W).map φ).f n) :=
  homComplexSystem_map_f_surjective k _ W
    (termwisePowTorsionProjective_groupStandardTotalSystem k N K hK) φ n

/-- The inverse system of Hom complexes `Hom^•(C_m^•, W_m)`, `C_m^•` the total complexes
`groupStandardTotalSystem`, satisfies the Mittag-Leffler condition in every degree: its
transitions are surjective in every degree. -/
lemma isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval (n : ℤ) :
    (homComplexSystem k (groupStandardTotalSystem.{w} N K) W ⋙
      HomologicalComplex.eval (ModuleCat.{max w u v} k) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{max w u v} k)).IsMittagLeffler :=
  isMittagLeffler_homComplexSystem_eval k _ W
    (termwisePowTorsionProjective_groupStandardTotalSystem k N K hK) n

/-- The degree-`n` components of the limit projections of the Hom complexes
`Hom^•(C_m^•, W_m)`, `C_m^•` the total complexes `groupStandardTotalSystem`, are surjective. -/
lemma groupStandardTotalSystem_homComplexLimit_π_f_surjective (m : ℕ) (n : ℤ) :
    Function.Surjective
      ((limit.π (homComplexSystem k (groupStandardTotalSystem.{w} N K) W) (Opposite.op m)).f n) :=
  homComplexLimit_π_f_surjective k _ W
    (termwisePowTorsionProjective_groupStandardTotalSystem k N K hK) m n

end GroupTotal

section SmoothTotal

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
  (hfree : UnderlyingPowTorsionProjectiveBelow N (K.quotientInvariantsComplexes H hK))

include hfree

/-- Harris's `C_m^{•,H}` (`quotientInvariantsTotalSystem`) satisfies
`TermwisePowTorsionProjective` when the underlying module of every level-`m` term of the
`H`-invariants in degree `q < N` is projective relative to objects killed by `ℓ ^ m`. -/
lemma termwisePowTorsionProjective_quotientInvariantsTotalSystem :
    TermwisePowTorsionProjective (K.quotientInvariantsTotalSystem N H hK) :=
  termwisePowTorsionProjective_groupStandardTotalSystem R N _ hfree

variable (W : DivisibleSystem (Rep.{max w uR uG} R (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the
complexes `quotientInvariantsTotalSystem`: the transitions of the inverse system of the `T_m(j)`
are surjective. -/
lemma quotientInvariantsTotalSystem_degree_homSystem_map_surjective (j : ℤ) {m m' : ℕᵒᵖ}
    (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R ((K.quotientInvariantsTotalSystem N H hK).degree j) W).map φ) :=
  groupStandardTotalSystem_degree_homSystem_map_surjective R N _ hfree W j φ

/-- The inverse system of the `T_m(j) = Hom(C_m^{j,H}, W_m)`, `C_m^{•,H}` the complexes
`quotientInvariantsTotalSystem`, satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_quotientInvariantsTotalSystem_degree_homSystem (j : ℤ) :
    (homSystem R ((K.quotientInvariantsTotalSystem N H hK).degree j) W ⋙
      CategoryTheory.forget (ModuleCat.{max w uR uG} R)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_degree_homSystem R N _ hfree W j

variable (W : DivisibleSystem (CochainComplex (Rep.{max w uR uG} R (G ⧸ H)) ℤ) ℓ)

/-- The inverse system of Hom complexes `Hom^•(C_m^{•,H}, W_m)`, `C_m^{•,H}` the complexes
`quotientInvariantsTotalSystem`, satisfies the Mittag-Leffler condition in every degree. -/
lemma isMittagLeffler_quotientInvariantsTotalSystem_homComplexSystem_eval (n : ℤ) :
    (homComplexSystem R (K.quotientInvariantsTotalSystem N H hK) W ⋙
      HomologicalComplex.eval (ModuleCat.{max w uR uG} R) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{max w uR uG} R)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval R N _ hfree W n

end SmoothTotal

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
  (hfree : UnderlyingPowTorsionProjectiveBelow (D + 2)
    (smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres))

include hfree

/-- Harris's `C_m^{•,H}` for the truncated smooth Godement resolutions
(`smoothGodementInvariantTotalSystem`) satisfies `TermwisePowTorsionProjective` when the
underlying module of every level-`m` `H`-invariant section term in degree `q < D + 2` is
projective relative to objects killed by `ℓ ^ m`. -/
lemma termwisePowTorsionProjective_smoothGodementInvariantTotalSystem :
    TermwisePowTorsionProjective (smoothGodementInvariantTotalSystem h T D H hterm hres) :=
  termwisePowTorsionProjective_groupStandardTotalSystem.{0} R (D + 2) _ hfree

variable (W : DivisibleSystem (Rep.{u} R (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the
complexes `smoothGodementInvariantTotalSystem`: the transitions of the inverse system of the
`T_m(j)` are surjective. -/
lemma smoothGodementInvariantTotalSystem_degree_homSystem_map_surjective (j : ℤ)
    {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R ((smoothGodementInvariantTotalSystem h T D H hterm hres).degree j) W).map
        φ) :=
  groupStandardTotalSystem_degree_homSystem_map_surjective.{0} R (D + 2) _ hfree W j φ

/-- The inverse system of the `T_m(j) = Hom(C_m^{j,H}, W_m)`, `C_m^{•,H}` the complexes
`smoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_smoothGodementInvariantTotalSystem_degree_homSystem (j : ℤ) :
    (homSystem R ((smoothGodementInvariantTotalSystem h T D H hterm hres).degree j) W ⋙
      CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_degree_homSystem.{0} R (D + 2) _ hfree W j

variable (W : DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℤ) ℓ)

/-- The inverse system of Hom complexes `Hom^•(C_m^{•,H}, W_m)`, `C_m^{•,H}` the complexes
`smoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler condition in every
degree. -/
lemma isMittagLeffler_smoothGodementInvariantTotalSystem_homComplexSystem_eval (n : ℤ) :
    (homComplexSystem R (smoothGodementInvariantTotalSystem h T D H hterm hres) W ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval.{0} R (D + 2) _ hfree W n

end SmoothGodement

section ProPSmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (hP : ProPInvariantsExactStatement.{u, u, u}) {p : ℕ} {H : Subgroup G} [H.Normal]
  [H.FiniteIndex] (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
  (hfree : UnderlyingPowTorsionProjectiveBelow (D + 2)
    (proPSmoothGodementTruncatedQuotientInvariantSectionsSystem h T D hP hH hR hterm hres))

include hfree

/-- Harris's `C_m^{•,H}` for the truncated smooth Godement resolutions and a normal pro-`p`
subgroup `H` of finite index (`proPSmoothGodementInvariantTotalSystem`) satisfies
`TermwisePowTorsionProjective` when the underlying module of every level-`m` `H`-invariant
section term in degree `q < D + 2` is projective relative to objects killed by `ℓ ^ m`. -/
lemma termwisePowTorsionProjective_proPSmoothGodementInvariantTotalSystem :
    TermwisePowTorsionProjective
      (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres) :=
  termwisePowTorsionProjective_groupStandardTotalSystem.{0} R (D + 2) _ hfree

variable (W : DivisibleSystem (Rep.{u} R (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the
complexes `proPSmoothGodementInvariantTotalSystem`: the transitions of the inverse system of
the `T_m(j)` are surjective. -/
lemma proPSmoothGodementInvariantTotalSystem_degree_homSystem_map_surjective (j : ℤ)
    {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R ((proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres).degree
        j) W).map φ) :=
  groupStandardTotalSystem_degree_homSystem_map_surjective.{0} R (D + 2) _ hfree W j φ

/-- The inverse system of the `T_m(j) = Hom(C_m^{j,H}, W_m)`, `C_m^{•,H}` the complexes
`proPSmoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_proPSmoothGodementInvariantTotalSystem_degree_homSystem (j : ℤ) :
    (homSystem R ((proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres).degree j)
      W ⋙ CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_degree_homSystem.{0} R (D + 2) _ hfree W j

variable (W : DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℤ) ℓ)

/-- The inverse system of Hom complexes `Hom^•(C_m^{•,H}, W_m)`, `C_m^{•,H}` the complexes
`proPSmoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler condition in every
degree. -/
lemma isMittagLeffler_proPSmoothGodementInvariantTotalSystem_homComplexSystem_eval (n : ℤ) :
    (homComplexSystem R (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres) W ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval.{0} R (D + 2) _ hfree W n

end ProPSmoothGodement

end DivisibleSystem

end Langlands.Cohomology
