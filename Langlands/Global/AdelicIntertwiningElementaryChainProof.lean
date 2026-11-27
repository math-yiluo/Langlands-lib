import Langlands.Global.AdelicStandardWeylSteps

/-! # Decomposition of intertwining operators into rank-one steps

Proof of `Langlands.Global.IntertwiningElementaryChainStatement` (Bernstein–Lapid §8.6;
Mœglin–Waldspurger I.1.8, II.1.6). A Weyl conjugation `(w, c)` from `P_I` to `P_I'` is replaced by
a normalizing representative whose Weyl element is right `W_I`-minimal; that element is a product
of rank-one steps along a chain of standard indices (`hasRankOneChain_of_right_minimal`); the steps
are lifted to normalizer points in the rational points of the Levis of `L_t ∪ {a_t}`. Each step
operator is invariant under the kernel of the root form of `a_t`, the composite Weyl parameter
carries the kernel of a root form of `P_I` into it, and the composite of the chain differs from `w`
by a rational point of `M_I`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

/-- The trivial Weyl conjugation of a subgroup to itself. -/
theorem AdelicGroupPoints.isWeylConjugation_one_id {F : Type u} [Field F]
    {G P M : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G} {l : M ⟶ P} :
    IsWeylConjugation p l p l (1 : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (𝟙 M) :=
  ⟨inferInstance, by rw [innerIso_one_inv, Category.id_comp, Category.comp_id]⟩

/-- **Decomposition into elementary symmetries** (Bernstein–Lapid §8.6; Mœglin–Waldspurger
I.1.8, II.1.6). -/
theorem intertwiningElementaryChain : IntertwiningElementaryChainStatement.{u} := by
  intro F _ _ G _ _ _ fam _ _ _ K hK I I' w c π _ hw hπ
  classical
  -- The Coxeter system of the relative Weyl group.
  obtain ⟨-, hfinB, CM, cs, h⟩ := relativeWeylCoxeter F G fam.connectedReductive fam.T fam.i
    fam.maximalSplit fam.ν fam.generic
  have : Fintype (SimpleRoot fam.i fam.ν) := Fintype.ofFinite _
  have hWS : ∀ L : Finset (SimpleRoot fam.i fam.ν),
      standardSubgroup cs L = standardRelativeWeylGroup fam.i fam.ν (rootSet fam.i fam.ν L) :=
    h.2.2.2.2
  obtain ⟨IL, hIL⟩ := fam.exists_rootSet_eq I
  obtain ⟨IM, hIM⟩ := fam.exists_rootSet_eq I'
  -- A normalizing representative `n₀ = w z₀`.
  obtain ⟨z₀, hn₀⟩ := fam.exists_normalizerPoints_mul_levi hw
  let n₀ : normalizerPoints fam.i := ⟨_, hn₀⟩
  have hw₀ := hw.mul_right_levi z₀
  have hc₀ : ∀ g, g ∈ standardSubgroup cs IM ↔
      (QuotientGroup.mk n₀ : relativeWeylGroup fam.i)⁻¹ * g * QuotientGroup.mk n₀ ∈
        standardSubgroup cs IL := by
    intro g
    rw [hWS, hWS, hIL, hIM]
    exact fam.mem_standardRelativeWeylGroup_iff_of_isWeylConjugation (n := n₀) hw₀ g
  -- The right `W_I`-minimal element `x` of the coset of `n₀`.
  obtain ⟨x, u, hu, hx₀, hxmin⟩ := exists_right_minimal_decomposition cs IL
    (QuotientGroup.mk n₀ : relativeWeylGroup fam.i)
  have hcx : ∀ g, g ∈ standardSubgroup cs IM ↔ x⁻¹ * g * x ∈ standardSubgroup cs IL := by
    intro g
    rw [hc₀, hx₀]
    constructor
    · intro h'
      have h'' := (standardSubgroup cs IL).mul_mem ((standardSubgroup cs IL).mul_mem hu h')
        ((standardSubgroup cs IL).inv_mem hu)
      simpa [mul_assoc] using h''
    · intro h'
      have h'' := (standardSubgroup cs IL).mul_mem
        ((standardSubgroup cs IL).mul_mem ((standardSubgroup cs IL).inv_mem hu) h') hu
      simpa [mul_assoc] using h''
  have hu' : u ∈ standardRelativeWeylGroup fam.i fam.ν (rootSet fam.i fam.ν IL) := by
    rw [← hWS]
    exact hu
  obtain ⟨m₀, hm₀, hm₀mk⟩ := (mem_standardRelativeWeylGroup_iff fam.i fam.ν).mp hu'
  let n' : normalizerPoints fam.i := n₀ * m₀⁻¹
  have hn'mk : (QuotientGroup.mk n' : relativeWeylGroup fam.i) = x := by
    change QuotientGroup.mk (n₀ * m₀⁻¹) = x
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hm₀mk, hx₀, mul_inv_cancel_right]
  -- The chain of rank-one steps.
  obtain ⟨m, Ls, as, gs, xs, h0, hlast, hxs0, hxslast, hstep⟩ :=
    hasRankOneChain_of_right_minimal cs (cs.length x) x IL IM rfl hxmin hcx
  let J : Fin m → StandardIndex F G fam.i fam.ν :=
    fun s => ⟨rootSet fam.i fam.ν (Ls s.succ), rootSet_subset fam.i fam.ν _⟩
  have hval : ∀ t : Fin (m + 1),
      ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t).val =
        rootSet fam.i fam.ν (Ls t) := by
    intro t
    refine Fin.cases ?_ (fun s => ?_) t
    · rw [Fin.cons_zero, h0, hIL]
    · rw [Fin.cons_succ]
  -- Lifts of the steps to normalizer points in the Levis of `L_t ∪ {a_t}`.
  have hlift : ∀ t : Fin m, ∃ nt : normalizerPoints fam.i,
      nt.val ∈ standardLeviPoints fam.i fam.ν
          (rootSet fam.i fam.ν (insert (as t) (Ls t.castSucc))) ∧
        (QuotientGroup.mk nt : relativeWeylGroup fam.i) = gs t := by
    intro t
    have hg := (hstep t).1.2.2.1
    rw [hWS] at hg
    exact (mem_standardRelativeWeylGroup_iff fam.i fam.ν).mp hg
  choose ns hns hnsmk using hlift
  have himage : ∀ t : Fin m,
      weylAction fam.i (ns t) ''
          ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t.castSucc).val =
        ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t.succ).val := by
    intro t
    rw [hval, hval]
    obtain ⟨-, -, -, hpos, hinto, honto⟩ := (hstep t).1
    exact weylAction_image_rootSet_of_simple_bijection h hpos hinto honto (ns t) (hnsmk t)
  have hcst : ∀ t : Fin m, ∃ c' : fam.M ((Fin.cons I J : Fin (m + 1) → _) t.succ) ⟶
      fam.M ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t.castSucc),
      IsWeylConjugation (fam.p _) (fam.l _) (fam.p _) (fam.l _) (ns t).val c' :=
    fun t => fam.exists_isWeylConjugation_of_image (ns t) (himage t)
  choose cst hcst using hcst
  -- Retractions and Levi decompositions.
  have hret : ∀ Jx : StandardIndex F G fam.i fam.ν, ∃ πx : fam.P Jx ⟶ fam.M Jx,
      fam.l Jx ≫ πx = 𝟙 _ ∧ IsIso (subgroupMultiplication (fam.l Jx) (fam.iU Jx)) := by
    intro Jx
    have : IsIso (subgroupMultiplication (fam.l Jx) (fam.iU Jx)) :=
      Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication (fam.rootPresentation Jx)
        fam.connectedReductive (fam.isUnipotentRadical Jx)
    exact ⟨leviRetraction (fam.l Jx) (fam.iU Jx) (fam.isUnipotentRadical Jx).1.isNormal,
      levi_comp_leviRetraction _ _ _, this⟩
  choose πr hπr hmult using hret
  -- Partial composites.
  let Wn : Fin (m + 1) → normalizerPoints fam.i := Fin.induction 1 (fun t Wt => ns t * Wt)
  have hWnsucc : ∀ t : Fin m, Wn t.succ = ns t * Wn t.castSucc := fun t => rfl
  let C : ∀ t : Fin (m + 1),
      fam.M ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t) ⟶ fam.M I :=
    Fin.induction (𝟙 (fam.M I)) (fun t Ct => cst t ≫ Ct)
  have hWC : ∀ t : Fin (m + 1), IsWeylConjugation (fam.p I) (fam.l I)
      (fam.p ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t))
      (fam.l ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t)) (Wn t).val (C t) := by
    intro t
    induction t using Fin.induction with
    | zero => exact isWeylConjugation_one_id
    | succ t ih => exact ih.comp (hcst t)
  have hmaps : ∀ t : Fin (m + 1), ∀ β ∈ I.val, weylAction fam.i (Wn t) β ∈
      ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t).val := by
    intro t
    induction t using Fin.induction with
    | zero =>
      intro β hβ
      change weylAction fam.i 1 β ∈ I.val
      rw [map_one]
      exact hβ
    | succ t ih =>
      intro β hβ
      rw [hWnsucc, map_mul, LinearEquiv.mul_apply, ← himage t]
      exact Set.mem_image_of_mem _ (ih β hβ)
  have hWnmk : ∀ t : Fin (m + 1), (QuotientGroup.mk (Wn t) : relativeWeylGroup fam.i) = xs t := by
    intro t
    induction t using Fin.induction with
    | zero => exact hxs0.symm
    | succ t ih => rw [hWnsucc, QuotientGroup.mk_mul, ih, hnsmk, (hstep t).2]
  -- The composite differs from `w` by a rational point of `M_I`.
  have hlastI : (Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) (Fin.last m) = I' :=
    Subtype.ext (by rw [hval, hlast, hIM])
  have hcent : (n'⁻¹ * Wn (Fin.last m)).val ∈ centralizerPoints fam.i := by
    have he : (QuotientGroup.mk n' : relativeWeylGroup fam.i) = QuotientGroup.mk (Wn (Fin.last m)) := by
      rw [hn'mk, hWnmk, hxslast]
    exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp he)
  have hy : w⁻¹ * (Wn (Fin.last m)).val ∈ standardLeviPoints fam.i fam.ν I.val := by
    have e : w⁻¹ * (Wn (Fin.last m)).val = (z₀ ≫ (fam.l I ≫ fam.p I).hom.hom) * (m₀.val)⁻¹ *
        (n'⁻¹ * Wn (Fin.last m)).val := by
      change w⁻¹ * (Wn (Fin.last m)).val = (z₀ ≫ (fam.l I ≫ fam.p I).hom.hom) * (m₀.val)⁻¹ *
        ((w * (z₀ ≫ (fam.l I ≫ fam.p I).hom.hom) * (m₀.val)⁻¹)⁻¹ * (Wn (Fin.last m)).val)
      group
    have h1 : z₀ ≫ (fam.l I ≫ fam.p I).hom.hom ∈ standardLeviPoints fam.i fam.ν I.val :=
      (fam.mem_standardLeviPoints_iff I _).mpr ⟨z₀, rfl⟩
    have h2 : m₀.val ∈ standardLeviPoints fam.i fam.ν I.val := hIL ▸ hm₀
    have h3 : (n'⁻¹ * Wn (Fin.last m)).val ∈ standardLeviPoints fam.i fam.ν I.val :=
      hIL ▸ centralizerPoints_le_levi fam.i fam.ν IL hcent
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)) h3
  obtain ⟨z, hz⟩ := (fam.mem_standardLeviPoints_iff I _).mp hy
  have hWz : (Wn (Fin.last m)).val = w * (z ≫ (fam.l I ≫ fam.p I).hom.hom) := by
    rw [hz, mul_inv_cancel_left]
  -- Assembly.
  refine ⟨m, J, fun t => (ns t).val, cst, fun t => (Wn t).val, C,
    fun t => πr ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t), rfl, rfl,
    fun t => ⟨rfl, rfl⟩, fun t => hπr _, fun t => hmult _, hcst, fun t => ?_, ?_⟩
  · have ha := (as t).property
    have haK : (as t).val ∉
        ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t.castSucc).val := by
      rw [hval]
      exact fun hmem => (hstep t).1.1 ((val_mem_rootSet fam.i fam.ν _ _).mp hmem)
    let S : StandardIndex F G fam.i fam.ν :=
      ⟨rootSet fam.i fam.ν (insert (as t) (Ls t.castSucc)), rootSet_subset fam.i fam.ν _⟩
    have hS : S.val = insert (as t).val
        ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t.castSucc).val := by
      rw [hval]
      exact rootSet_insert _ _
    have hL'S : ((Fin.cons I J : Fin (m + 1) → StandardIndex F G fam.i fam.ν) t.succ).val ⊆
        S.val := by
      rw [hval]
      exact (rootSet_subset_iff fam.i fam.ν _ _).mpr (hstep t).1.2.1
    refine ⟨_, fam.restrict_simple_mem_unipotentRoots ha haK, ⟨0, fun mu nu _ _ hnu ψ g =>
      fam.intertwiningOperator_add_of_rootFunctional_eq_zero hK ha hS hL'S (hns t) (hcst t)
        (hπr _) ψ mu nu hnu g⟩, ?_⟩
    exact fam.exists_unipotentRoot_weylParameter (Wn t.castSucc).property (hWC t.castSucc)
      (hπr _) (hmaps t.castSucc) ha haK
  · exact ⟨0, fun mu _ ψ hψ g => fam.intertwiningOperator_eq_of_eq_mul_levi hK hlastI.symm hw
      (hWC (Fin.last m)) hπ (hπr _) z hWz ψ hψ mu g⟩

end Langlands.Global
