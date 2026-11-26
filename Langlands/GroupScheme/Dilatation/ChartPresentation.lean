import Langlands.GroupScheme.Dilatation.ChartRegular
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Polynomial presentations for regular dilatation charts -/

noncomputable section

open MvPolynomial RingTheory.Sequence

namespace Langlands.GroupScheme.Dilatation

variable {A : Type*} [CommRing A]

private def chartEquations (t : A) (xs : List A) : List (MvPolynomial (Fin xs.length) A) :=
  List.ofFn fun i => C (xs.get i) - C t * X i

/-- The polynomial chart imposing one equation `t * T_i = x_i` for each generator. -/
abbrev chartPresentation (t : A) (xs : List A) :=
  MvPolynomial (Fin xs.length) A ⧸ Ideal.ofList (chartEquations t xs)

private abbrev chartMk (t : A) (xs : List A) :=
  Ideal.Quotient.mkₐ A (Ideal.ofList (chartEquations t xs))

private theorem chart_relation (t : A) (xs : List A) (i : Fin xs.length) :
    algebraMap A (chartPresentation t xs) (xs.get i) =
      algebraMap A (chartPresentation t xs) t * chartMk t xs (X i) := by
  change chartMk t xs (C (xs.get i)) = chartMk t xs (C t) * chartMk t xs (X i)
  rw [← map_mul, ← sub_eq_zero, ← map_sub, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.subset_span
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

private theorem ringEquiv_weaklyRegular {B : Type*} [CommRing B] (e : A ≃+* B)
    {xs : List A} (h : IsWeaklyRegular B (xs.map e)) : IsWeaklyRegular A xs :=
  (e.toAddEquiv.isWeaklyRegular_congr <| List.forall₂_map_right_iff.mpr <|
    List.forall₂_same.mpr fun r _ x => e.map_mul r x).mpr h

/-- If the generators are weakly regular modulo `t`, the same denominator acts
regularly in the polynomial chart. -/
theorem chartPresentation_regular (t : A) (xs : List A) (ht : IsSMulRegular A t)
    (hxs : IsWeaklyRegular (A ⧸ Ideal.span {t}) (xs.map (Ideal.Quotient.mk (Ideal.span {t})))) :
    IsSMulRegular (chartPresentation t xs) (algebraMap A (chartPresentation t xs) t) := by
  let P := MvPolynomial (Fin xs.length) A
  let J : Ideal A := Ideal.span {t}
  let q := Ideal.Quotient.mk J
  have hJ : J.map (C : A →+* P) = Ideal.span {C t} := by rw [Ideal.map_span, Set.image_singleton]
  let e : (P ⧸ Ideal.span {C t}) ≃+* MvPolynomial (Fin xs.length) (A ⧸ J) :=
    (Ideal.quotEquivOfEq hJ.symm).trans
      (quotientEquivQuotientMvPolynomial (σ := Fin xs.length) J).symm.toRingEquiv
  have he (p : P) : e (Ideal.Quotient.mk (Ideal.span {C t}) p) = MvPolynomial.map q p := by
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, map_eq_eval₂Hom_C_comp]
    rfl
  have heq : ((chartEquations t xs).map (Ideal.Quotient.mk (Ideal.span {C t}))).map e =
      (xs.map q).map (algebraMap (A ⧸ J) (MvPolynomial (Fin xs.length) (A ⧸ J))) := by
    rw [List.map_map, chartEquations, List.map_ofFn, List.map_map]
    change List.ofFn _ = xs.map (fun a => C (q a))
    rw [← List.ofFn_getElem_eq_map]
    congr 1
    funext i
    simp only [Function.comp_apply, he, map_sub, map_mul, map_C, map_X]
    have ht0 : q t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))
    simp [ht0]
  have hreg := ht.of_flat (S := P)
  refine regular_quotient_ofList_of_regular_mod (C t) (chartEquations t xs) hreg ?_
  exact ringEquiv_weaklyRegular e (heq.symm ▸ hxs.of_flat)

/-- Modulo the denominator, the chart equations kill the constants generating the
centre ideal. -/
private theorem chartEquations_sup_span (t : A) (xs : List A) (I : Ideal A)
    (hgen : Ideal.span {t} ⊔ Ideal.ofList xs = I) :
    Ideal.ofList (chartEquations t xs) ⊔ Ideal.span {C t} = I.map (C (σ := Fin xs.length)) := by
  let P := MvPolynomial (Fin xs.length) A
  have hmul (i : Fin xs.length) : C t * X i ∈ Ideal.span ({C t} : Set P) :=
    Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  rw [← hgen, Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_ofList]
  refine le_antisymm (sup_le ?_ le_sup_left) (sup_le le_sup_right ?_)
  · apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact Ideal.sub_mem _ (Submodule.mem_sup_right (Ideal.subset_span
      (s := {a : P | a ∈ xs.map C}) (List.mem_map.mpr ⟨_, List.get_mem xs i, rfl⟩)))
      (Submodule.mem_sup_left (hmul i))
  · apply Ideal.span_le.mpr
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
    have heq : C (xs.get i) - C t * X i ∈ Ideal.ofList (chartEquations t xs) :=
      Ideal.subset_span (s := {a : P | a ∈ chartEquations t xs}) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    rw [← sub_add_cancel (C (xs.get i)) (C t * X i)]
    exact Ideal.add_mem _ (Submodule.mem_sup_left heq) (Submodule.mem_sup_right (hmul i))

private def chartReductionEquiv (t : A) (xs : List A) (I : Ideal A)
    (hgen : Ideal.span {t} ⊔ Ideal.ofList xs = I) :
    (chartPresentation t xs ⧸ Ideal.span {algebraMap A (chartPresentation t xs) t}) ≃+*
      MvPolynomial (Fin xs.length) (A ⧸ I) := by
  let P := MvPolynomial (Fin xs.length) A
  let J := Ideal.ofList (chartEquations t xs)
  let Jt : Ideal P := Ideal.span {C t}
  have h : Ideal.span {algebraMap A (chartPresentation t xs) t} =
      Jt.map (Ideal.Quotient.mk J) := by rw [Ideal.map_span, Set.image_singleton]; rfl
  exact (Ideal.quotEquivOfEq h).trans ((DoubleQuot.quotQuotEquivQuotSup J Jt).trans
    ((Ideal.quotEquivOfEq (chartEquations_sup_span t xs I hgen)).trans
      (quotientEquivQuotientMvPolynomial (σ := Fin xs.length) I).symm.toRingEquiv))

private theorem chartReductionEquiv_mk (t : A) (xs : List A) (I : Ideal A)
    (hgen : Ideal.span {t} ⊔ Ideal.ofList xs = I) (a : A) :
    chartReductionEquiv t xs I hgen (Ideal.Quotient.mk
      (Ideal.span {algebraMap A (chartPresentation t xs) t}) (algebraMap A _ a)) =
        C (Ideal.Quotient.mk I a) := by
  simp only [chartReductionEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  let J := Ideal.ofList (chartEquations t xs)
  let Jt : Ideal (MvPolynomial (Fin xs.length) A) := Ideal.span {C t}
  change (quotientEquivQuotientMvPolynomial (σ := Fin xs.length) I).symm.toRingEquiv
    (Ideal.quotEquivOfEq (chartEquations_sup_span t xs I hgen)
      (DoubleQuot.quotQuotEquivQuotSup J Jt (DoubleQuot.quotQuotMk J Jt (C a)))) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]
  change eval₂ (C.comp (Ideal.Quotient.mk I)) X (C a) = _
  rw [eval₂_C, RingHom.comp_apply]

section Residue

variable {R : Type*} [CommRing R] [Algebra R A]

/-- The quotient of the affine dilatation algebra by the base denominator. -/
abbrev blowupResidue (r : R) (I : Ideal A) :=
  blowupAlgebra r I ⧸ Ideal.span {algebraMap R (blowupAlgebra r I) r}

/-- The centre acts on the quotient of the dilatation algebra by the denominator. -/
def blowupResidueMap (r : R) (I : Ideal A) : A ⧸ I →+* blowupResidue r I :=
  Ideal.quotientMap _ (algebraMap A (blowupAlgebra r I)) (by
    rw [← Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_apply R A (blowupAlgebra r I)]
    exact ideal_map_le_span (algebraMap R A r) I)

instance blowupResidueAlgebra (r : R) (I : Ideal A) : Algebra (A ⧸ I) (blowupResidue r I) :=
  @RingHom.toAlgebra (A ⧸ I) (blowupResidue r I) _ _ (blowupResidueMap r I)

@[simp] theorem algebraMap_blowupResidue_mk (r : R) (I : Ideal A) (a : A) :
    algebraMap (A ⧸ I) (blowupResidue r I) (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R (blowupAlgebra r I) r})
        (algebraMap A (blowupAlgebra r I) a) := rfl

end Residue

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R A]

private theorem dvrFlat_of_uniformizer_regular {B : Type*} [CommRing B] [Algebra R B]
    {r : R} (hr : Irreducible r) (hreg : IsSMulRegular B r) : Module.Flat R B := by
  let : Module.IsTorsionFree R B := ⟨fun x hx => by
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx.ne_zero hr
    exact IsSMulRegular.of_mul (a := ↑u) (by
      rw [mul_comm, hu]
      exact hreg.pow n)⟩
  infer_instance

variable [Module.Flat R A] {r : R}

private def chartToBlowup (I : Ideal A) (xs : List A) (hx : Ideal.ofList xs ≤ I) :
    chartPresentation (algebraMap R A r) xs →ₐ[A] blowupAlgebra r I := by
  let f := fun i : Fin xs.length => dividedElement (algebraMap R A r) I
      ⟨xs.get i, hx (Ideal.subset_span (s := {a : A | a ∈ xs}) (List.get_mem xs i))⟩
  refine Ideal.Quotient.liftₐ _ (aeval f) ?_
  intro p hp
  have hp' : p ∈ RingHom.ker (aeval f).toRingHom := by
    apply Ideal.span_le.mpr ?_ hp
    intro p' hp'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp'
    change aeval f (C (xs.get i) - C (algebraMap R A r) * X i) = 0
    rw [map_sub, map_mul, aeval_C, aeval_C, aeval_X, sub_eq_zero]
    let a : I := ⟨xs.get i, hx (Ideal.subset_span (s := {a : A | a ∈ xs}) (List.get_mem xs i))⟩
    exact (mul_dividedElement (algebraMap R A r) I a).symm
  exact hp'

/-- With regular centre equations modulo the uniformizer, the polynomial chart
is the affine dilatation algebra, compatibly with the map from the original ring. -/
def chartEquivBlowup (hr : Irreducible r) (I : Ideal A) (xs : List A)
    (hgen : Ideal.span {algebraMap R A r} ⊔ Ideal.ofList xs = I)
    (hxs : IsWeaklyRegular (A ⧸ Ideal.span {algebraMap R A r})
      (xs.map (Ideal.Quotient.mk (Ideal.span {algebraMap R A r})))) :
    chartPresentation (algebraMap R A r) xs ≃ₐ[A] blowupAlgebra r I := by
  let t := algebraMap R A r
  let P := chartPresentation t xs
  have ht : IsSMulRegular A t := by
    intro x y h
    apply smul_right_injective A hr.ne_zero
    simpa only [Algebra.smul_def, t, Algebra.algebraMap_self_apply] using h
  have hreg := chartPresentation_regular t xs ht hxs
  let : Module.Flat R P := dvrFlat_of_uniformizer_regular hr (by
    intro x y h
    apply hreg
    simpa only [Algebra.smul_def, smul_eq_mul, IsScalarTower.algebraMap_apply R A P] using h)
  let F : P →ₐ[A] blowupAlgebra r I :=
    chartToBlowup I xs (hgen ▸ le_sup_right)
  let q : A →ₐ[R] P := IsScalarTower.toAlgHom R A P
  have hle : I ≤ Ideal.comap q.toRingHom (Ideal.span {algebraMap R P r}) := by
    rw [← hgen, sup_le_iff, Ideal.span_le, Ideal.span_le]
    refine ⟨?_, ?_⟩
    · rintro _ rfl
      exact Ideal.subset_span (Set.mem_singleton _)
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact Ideal.mem_span_singleton.mpr ⟨chartMk t xs (X i), chart_relation t xs i⟩
  have hI (a : A) (ha : a ∈ I) : q a ∈ Ideal.span {algebraMap R P r} := hle ha
  let L := liftBlowup hr.ne_zero I q hI
  let G : blowupAlgebra r I →ₐ[A] P :=
    { L.toRingHom with commutes' := fun a => DFunLike.congr_fun (liftBlowup_comp hr.ne_zero I q hI) a }
  refine AlgEquiv.ofAlgHom F G ?_ ?_
  · have he : ((F.comp G).restrictScalars R) = AlgHom.id R (blowupAlgebra r I) := by
      apply blowupMap_ext hr.ne_zero I
      exact AlgHom.ext fun a => (F.comp G).commutes a
    exact AlgHom.ext fun b => DFunLike.congr_fun he b
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change G (F (chartMk t xs (X i))) = chartMk t xs (X i)
    apply hreg
    change algebraMap A P t * G (F (chartMk t xs (X i))) =
      algebraMap A P t * chartMk t xs (X i)
    calc
      _ = G (F (algebraMap A P t * chartMk t xs (X i))) := by
        rw [map_mul, map_mul, F.commutes, G.commutes]
      _ = _ := by rw [← chart_relation, F.commutes, G.commutes, chart_relation]

/-- Modulo the uniformizer a regular dilatation chart is the polynomial algebra
over the centre. -/
def blowupResidueEquivPolynomial (hr : Irreducible r) (I : Ideal A) (xs : List A)
    (hgen : Ideal.span {algebraMap R A r} ⊔ Ideal.ofList xs = I)
    (hxs : IsWeaklyRegular (A ⧸ Ideal.span {algebraMap R A r})
      (xs.map (Ideal.Quotient.mk (Ideal.span {algebraMap R A r})))) :
    blowupResidue r I ≃ₐ[A ⧸ I] MvPolynomial (Fin xs.length) (A ⧸ I) := by
  let t := algebraMap R A r
  let P := chartPresentation t xs
  let B := blowupAlgebra r I
  let e := chartEquivBlowup hr I xs hgen hxs
  have hmap : Ideal.span {algebraMap R B r} =
      (Ideal.span {algebraMap A P t}).map e.toRingEquiv.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {algebraMap R B r} = Ideal.span {e (algebraMap A P t)}
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  let eq := Ideal.quotientEquiv _ _ e.toRingEquiv hmap
  let ef := chartReductionEquiv t xs I hgen
  refine AlgEquiv.ofRingEquiv (f := eq.symm.trans ef) ?_
  intro z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have he : eq.symm (Ideal.Quotient.mk (Ideal.span {algebraMap R B r}) (algebraMap A B a)) =
      Ideal.Quotient.mk (Ideal.span {algebraMap A P t}) (algebraMap A P a) :=
    (Ideal.quotientEquiv_symm_mk _ _ e.toRingEquiv hmap _).trans
      (congrArg (Ideal.Quotient.mk (Ideal.span {algebraMap A P t})) (e.symm.commutes a))
  exact (congrArg ef he).trans (chartReductionEquiv_mk t xs I hgen a)

end DVR

end Langlands.GroupScheme.Dilatation
