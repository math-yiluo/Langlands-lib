import Langlands.Global.Arithmetic.HarrisProposition48MackeyData
import Langlands.Global.Arithmetic.HarrisDatumArchimedean
import Langlands.Global.HeckeCharacterTransport
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation

/-! # Infinity types and character pullback in the Harris Mackey step -/

noncomputable section

namespace Langlands.Global.Harris

open NumberField InfinitePlace.Completion AdelicFunctoriality
open scoped NumberField.LiesOver InfiniteExtension

section Infinite

variable {K L M : Type*} [Field K] [Field L] [Field M]

private def completedMap (f : K →+* L) (v : InfinitePlace K) (w : InfinitePlace L)
    (h : w.comap f = v) : v.Completion →+* w.Completion := by
  subst v
  exact infiniteCompletionMap f w

private theorem completedMap_coe (f : K →+* L) (v : InfinitePlace K) (w : InfinitePlace L)
    (h : w.comap f = v) (x : K) :
    completedMap f v w h (algebraMap K v.Completion x) =
      algebraMap L w.Completion (f x) := by
  subst v
  exact infiniteCompletionMap_coe f w x

private theorem continuous_completedMap (f : K →+* L) (v : InfinitePlace K)
    (w : InfinitePlace L) (h : w.comap f = v) : Continuous (completedMap f v w h) := by
  subst v
  exact continuous_infiniteCompletionMap f w

private theorem eq_onCompletion {v : InfinitePlace K} {T : Type*}
    [TopologicalSpace T] [T2Space T] {f g : v.Completion → T}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : K, f (algebraMap K v.Completion x) = g (algebraMap K v.Completion x)) :
    f = g :=
  (denseRange_coe v).equalizer hf hg (funext fun x => h (WithAbs.equiv v.1 x))

private theorem completedMap_comp {f : K →+* L} {g : L →+* M} {h : K →+* M}
    (hh : g.comp f = h) (v : InfinitePlace K) (w : InfinitePlace L) (z : InfinitePlace M)
    (hv : w.comap f = v) (hw : z.comap g = w) (hz : z.comap h = v) :
    (completedMap g w z hw).comp (completedMap f v w hv) = completedMap h v z hz := by
  apply DFunLike.ext'
  refine eq_onCompletion (f := completedMap g w z hw ∘ completedMap f v w hv)
    (g := completedMap h v z hz) ((continuous_completedMap g w z hw).comp
    (continuous_completedMap f v w hv)) (continuous_completedMap h v z hz) fun x => ?_
  simp only [Function.comp_apply, completedMap_coe]
  exact congrArg (algebraMap M z.Completion) (RingHom.congr_fun hh x)

private theorem completedMap_id (v : InfinitePlace K) (h : v.comap (RingHom.id K) = v)
    (x : v.Completion) : completedMap (RingHom.id K) v v h x = x := by
  apply congrFun (eq_onCompletion (continuous_completedMap _ _ _ _) continuous_id ?_)
  intro y
  rw [completedMap_coe, RingHom.id_apply, id_eq]

private theorem completedMap_algebra [Algebra K L] (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] :
    completedMap (algebraMap K L) v w (InfinitePlace.LiesOver.comap_eq w v) =
      LiesOver.completionMap (v := v) (w := w) := by
  apply DFunLike.ext'
  refine eq_onCompletion (continuous_completedMap _ _ _ _) LiesOver.continuous_completionMap
    fun x => ?_
  rw [completedMap_coe]
  exact IsScalarTower.algebraMap_apply K v.Completion w.Completion x

private theorem completionEmbedding_map (f : K →+* L) (v : InfinitePlace K) (w : InfinitePlace L)
    (h : w.comap f = v) (c : v.Completion →+* ℂ) (hc : Continuous c)
    (he : ∀ x : K, c (algebraMap K v.Completion x) = w.embedding (f x)) (x : v.Completion) :
    extensionEmbedding w (completedMap f v w h x) = c x := by
  refine congrFun (eq_onCompletion ((isometry_extensionEmbedding w).continuous.comp
    (continuous_completedMap f v w h)) hc ?_) x
  intro y
  simp only [Function.comp_apply, completedMap_coe]
  rw [he y]
  exact extensionEmbedding_coe w (WithAbs.toAbs w.1 (f y))

private theorem embedding_over (f : K →+* L) (v : InfinitePlace K) (w : InfinitePlace L)
    (h : w.comap f = v) :
    v.embedding = w.embedding.comp f ∨
      ComplexEmbedding.conjugate v.embedding = w.embedding.comp f := by
  apply InfinitePlace.mk_eq_iff.mp
  rw [InfinitePlace.mk_embedding, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding, h]

private theorem completionEmbedding_of_eq (f : K →+* L) (v : InfinitePlace K)
    (w : InfinitePlace L) (h : w.comap f = v) (e : v.embedding = w.embedding.comp f)
    (x : v.Completion) :
    extensionEmbedding w (completedMap f v w h x) = extensionEmbedding v x :=
  completionEmbedding_map f v w h (extensionEmbedding v)
    (isometry_extensionEmbedding v).continuous
    (fun z => (extensionEmbedding_coe v (WithAbs.toAbs v.1 z)).trans (RingHom.congr_fun e z)) x

private theorem completionEmbedding_of_conjugate_eq (f : K →+* L) (v : InfinitePlace K)
    (w : InfinitePlace L) (h : w.comap f = v)
    (e : ComplexEmbedding.conjugate v.embedding = w.embedding.comp f) (x : v.Completion) :
    extensionEmbedding w (completedMap f v w h x) = star (extensionEmbedding v x) := by
  refine completionEmbedding_map f v w h (ComplexEmbedding.conjugate (extensionEmbedding v))
    (continuous_star.comp (isometry_extensionEmbedding v).continuous) (fun z => ?_) x
  change star (extensionEmbedding v (algebraMap K v.Completion z)) = _
  exact (congrArg star (extensionEmbedding_coe v (WithAbs.toAbs v.1 z))).trans
    (RingHom.congr_fun e z)

private theorem completedMap_surjective [IsTotallyComplex K] (f : K →+* L)
    (v : InfinitePlace K) (w : InfinitePlace L) (h : w.comap f = v) :
    Function.Surjective (completedMap f v w h) := by
  have hg := surjective_extensionEmbedding_of_isComplex (IsTotallyComplex.isComplex v)
  intro y
  rcases embedding_over f v w h with e | e
  · obtain ⟨x, hx⟩ := hg (extensionEmbedding w y)
    exact ⟨x, (extensionEmbedding w).injective ((completionEmbedding_of_eq f v w h e x).trans hx)⟩
  · obtain ⟨x, hx⟩ := hg (star (extensionEmbedding w y))
    refine ⟨x, (extensionEmbedding w).injective ((completionEmbedding_of_conjugate_eq f v w h e x).trans ?_)⟩
    rw [hx, star_star]

private theorem liesOver_of_comap_eq [Algebra K L] {v : InfinitePlace K}
    {w : InfinitePlace L} (h : w.comap (algebraMap K L) = v) : w.LiesOver v :=
  ⟨by ext x; exact InfinitePlace.comp_of_comap_eq h x⟩

end Infinite

section Conjugation

open IsDedekindDomain Complex

private theorem denseRange_finiteCompletionProduct (K : Type*) [Field K] [NumberField K] :
    DenseRange (fun x : K => fun p : FinitePlace K => algebraMap K (FiniteCompletion K p) x) := by
  classical
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨a, ha⟩ := hne
  obtain ⟨S, V, hV, hVU⟩ := isOpen_pi_iff.mp hU a ha
  obtain ⟨x, hx, _⟩ := exists_algebraMap_mem_open S (fun p => V p.1)
    (fun p => (hV p.1 p.2).1) (fun p => ⟨a p.1, (hV p.1 p.2).2⟩)
    (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.univ_nonempty)
  exact ⟨_, hVU (fun p hp => hx ⟨p, hp⟩), x, rfl⟩

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

private theorem adeleNorm_equiv (eK : K ≃+* K) (eL : L ≃+* L)
    (he : (algebraMap K L).comp eK.toRingHom = eL.toRingHom.comp (algebraMap K L))
    (x : AdeleRing (NumberField.RingOfIntegers L) L) :
    adeleNorm (K := K) (adeleEquiv eL x) = adeleEquiv eK (adeleNorm (K := K) x) := by
  have hnorm (y : L) : Algebra.norm K (eL y) = eK (Algebra.norm K y) := by
    rw [Algebra.norm_eq_of_equiv_equiv eK eL he y, RingEquiv.apply_symm_apply]
  apply Prod.ext
  · have hdiag (y : L) : infiniteAdeleNorm (K := K) (algebraMap L (InfiniteAdeleRing L) y) =
        algebraMap K (InfiniteAdeleRing K) (Algebra.norm K y) :=
      congrArg Prod.fst (adeleNorm_principal (K := K) y)
    refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap L).equalizer
      ((continuous_infiniteAdeleNorm (K := K) (L := L)).comp (continuous_infiniteAdeleEquiv eL))
      ((continuous_infiniteAdeleEquiv eK).comp (continuous_infiniteAdeleNorm (K := K) (L := L)))
      ?_) x.1
    funext y
    simp only [Function.comp_apply, infiniteAdeleEquiv_diagonal, hdiag, hnorm]
  · apply FiniteAdeleRing.ext
    intro p
    let transported (z : (q : FinitePlace L) → FiniteCompletion L q) (q : FinitePlace L) :=
      finiteCompletionEquiv eL q (z (finitePlaceEquiv eL q))
    have hcontinuous : Continuous transported := continuous_pi fun q =>
      (continuous_finiteCompletionEquiv eL q).comp (continuous_apply (finitePlaceEquiv eL q))
    have hdiag (q : FinitePlace K) (y : L) :
        finiteNormComponent q (fun r => algebraMap L (FiniteCompletion L r) y) =
          algebraMap K (FiniteCompletion K q) (Algebra.norm K y) :=
      congrArg (fun z : AdeleRing (NumberField.RingOfIntegers K) K => z.2 q)
        (adeleNorm_principal (K := K) y)
    refine congrFun ((denseRange_finiteCompletionProduct L).equalizer
      ((continuous_finiteNormComponent (L := L) p).comp hcontinuous)
      ((continuous_finiteCompletionEquiv eK p).comp
        (continuous_finiteNormComponent (L := L) (finitePlaceEquiv eK p))) ?_) (fun r => x.2 r)
    funext y
    have hy : transported (fun r => algebraMap L (FiniteCompletion L r) y) =
        fun r => algebraMap L (FiniteCompletion L r) (eL y) :=
      funext fun r => finiteCompletionEquiv_coe eL r y
    simp only [Function.comp_apply, hy, hdiag, finiteCompletionEquiv_coe, hnorm]

private theorem ideleClassNorm_equiv (eK : K ≃+* K) (eL : L ≃+* L)
    (he : (algebraMap K L).comp eK.toRingHom = eL.toRingHom.comp (algebraMap K L))
    (x : IdeleClasses L) :
    ideleClassNorm (K := K) (ideleClassEquiv eL x) =
      ideleClassEquiv eK (ideleClassNorm (K := K) x) := by
  induction x using Quotient.inductionOn with
  | h y =>
    simp only [ideleClassEquiv_mk, ideleClassNorm_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    exact adeleNorm_equiv eK eL he y.val

omit [Algebra K L] in
private theorem map_complexConj [IsCMField K] [IsCMField L] (f : K →+* L) (x : K) :
    f (IsCMField.complexConj K x) = IsCMField.complexConj L (f x) := by
  let σ : L →+* ℂ := Classical.choice inferInstance
  apply σ.injective
  exact (IsCMField.complexEmbedding_complexConj K (σ.comp f) x).trans
    (IsCMField.complexEmbedding_complexConj L σ (f x)).symm

end Conjugation

section Character

universe u

variable {T : Type*} {A C : Type u} [Field T] [NumberField T] [Field A] [NumberField A]
    [Field C] [NumberField C] [Algebra A C] [IsTotallyComplex A]

private theorem normComp_comap_component (e : T ≃+* A) (χ : HeckeCharacter T)
    (w : InfinitePlace C) (v : InfinitePlace T)
    (h : w.comap ((algebraMap A C).comp e.toRingHom) = v) (x : v.Completionˣ) :
    (HeckeCharacter.normComp (L := C) (HeckeCharacter.comap e.symm χ)).infiniteComponent w
      (Units.map (completedMap ((algebraMap A C).comp e.toRingHom) v w h).toMonoidHom x) =
      χ.infiniteComponent v x := by
  let p := infinitePlaceEquiv e.symm v
  have hp : w.comap (algebraMap A C) = p := by
    ext a
    change w (algebraMap A C a) = v (e.symm a)
    rw [← h, InfinitePlace.comap_apply, RingHom.comp_apply]
    exact congrArg (fun z : A => w (algebraMap A C z)) (e.apply_symm_apply a).symm
  let : w.LiesOver p := liesOver_of_comap_eq hp
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id T := by
    ext t
    exact e.symm_apply_apply t
  have hv : p.comap e.toRingHom = v := by
    change v.comap (e.symm.toRingHom.comp e.toRingHom) = v
    rw [he, InfinitePlace.comap_id]
  let y := Units.map (completedMap e.toRingHom v p hv).toMonoidHom x
  let q : InfinitePlacesAbove C p := ⟨w, inferInstance⟩
  have hy :
      Units.map (LiesOver.completionMap (v := p) (w := w)).toMonoidHom y =
        Units.map (completedMap ((algebraMap A C).comp e.toRingHom) v w h).toMonoidHom x := by
    apply Units.ext
    rw [← completedMap_algebra p w]
    exact RingHom.congr_fun (completedMap_comp rfl v p w _ hp h) x.val
  rw [← hy]
  change (HeckeCharacter.comap e.symm χ) (ideleClassNorm (K := A) (L := C)
    (NumberField.IdeleClassGroup.ofCompletion (NumberField.RingOfIntegers C) C q.1
      (Units.map (LiesOver.completionMap (v := p) (w := w)).toMonoidHom y))) = _
  rw [ideleClassNorm_ofCompletion p q]
  have hn : InfiniteExtension.localUnitNorm p w
      (Units.map (LiesOver.completionMap (v := p) (w := w)).toMonoidHom y) = y := by
    apply Units.ext
    have hu : w.IsUnramified A := InfinitePlace.isUnramified_iff.mpr
      (Or.inr (hp.symm ▸ IsTotallyComplex.isComplex p))
    change InfiniteExtension.localNorm p w (LiesOver.completionMap y.val) = y.val
    rw [InfiniteExtension.localNorm_algebraMap, hu.finrank_eq_one p, pow_one]
  change (HeckeCharacter.comap e.symm χ).infiniteComponent p
    (InfiniteExtension.localUnitNorm p w
      (Units.map (LiesOver.completionMap (v := p) (w := w)).toMonoidHom y)) = _
  rw [hn, HeckeCharacter.comap_infiniteComponent e.symm χ v y]
  apply congrArg (χ.infiniteComponent v)
  apply Units.ext
  change completedMap e.symm.toRingHom p v rfl (completedMap e.toRingHom v p _ x.val) = _
  exact (RingHom.congr_fun (completedMap_comp he v p v _ rfl v.comap_id) x.val).trans
    (completedMap_id v v.comap_id x.val)

private theorem isAlgebraicAfterTwist_normComp_comap [IsTotallyComplex T] [IsTotallyComplex C]
    (e : T ≃+* A) (χ : HeckeCharacter T) (b : ℕ) (hχ : IsAlgebraicAfterTwist b χ) :
    IsAlgebraicAfterTwist b (HeckeCharacter.normComp (L := C) (HeckeCharacter.comap e.symm χ)) := by
  classical
  obtain ⟨t, ht⟩ := hχ
  let f := (algebraMap A C).comp e.toRingHom
  let s : InfinityType C := fun σ => t (σ.comp f)
  let ψ := HeckeCharacter.normComp (L := C) (HeckeCharacter.comap e.symm χ)
  have hlocal (w : InfinitePlace C) (y : w.Completionˣ) :
      (ψ.infiniteComponent w y : ℂ) * ((‖extensionEmbedding w y‖ : ℝ) : ℂ) ^ b =
        (extensionEmbedding w y) ^ s w.embedding *
          star (extensionEmbedding w y) ^ s (ComplexEmbedding.conjugate w.embedding) := by
    let v := w.comap f
    obtain ⟨x₀, hx₀⟩ := completedMap_surjective f v w rfl y.val
    have hx₀ne : x₀ ≠ 0 := by
      intro h
      exact y.ne_zero (hx₀.symm.trans (h ▸ map_zero _))
    let x := Units.mk0 x₀ hx₀ne
    have hy : Units.map (completedMap f v w rfl).toMonoidHom x = y := Units.ext hx₀
    rw [← hy]
    change ((HeckeCharacter.normComp (L := C) (HeckeCharacter.comap e.symm χ)).infiniteComponent
      w (Units.map (completedMap f v w rfl).toMonoidHom x) : ℂ) * _ = _
    rw [normComp_comap_component]
    have hx := ht (HarrisDatum.single v x)
    rw [Finset.prod_pow, HarrisDatum.norm_coordinate_single, HarrisDatum.toCharacter_single,
      ← HarrisDatum.infiniteComponent_eq_atInfinity] at hx
    change _ * ((‖extensionEmbedding w (completedMap f v w rfl x.val)‖ : ℝ) : ℂ) ^ b =
      (extensionEmbedding w (completedMap f v w rfl x.val)) ^ s w.embedding *
        star (extensionEmbedding w (completedMap f v w rfl x.val)) ^
          s (ComplexEmbedding.conjugate w.embedding)
    rcases embedding_over f v w rfl with h | h
    · simpa only [s, completionEmbedding_of_eq f v w rfl h, HarrisDatum.conjugate_comp, ← h] using hx
    · have hn : ‖star (extensionEmbedding v x.val)‖ = ‖extensionEmbedding v x.val‖ :=
        Complex.norm_conj _
      rw [completionEmbedding_of_conjugate_eq f v w rfl h, hn, star_star]
      simpa only [s, HarrisDatum.conjugate_comp, ← h,
        ComplexEmbedding.involutive_conjugate T v.embedding,
        mul_comm (extensionEmbedding v x.val ^ t v.embedding)] using hx
  refine ⟨s, fun z => ?_⟩
  let y (w : InfinitePlace C) : w.Completionˣ :=
    Units.map (Pi.evalRingHom (fun w : InfinitePlace C => w.Completion) w).toMonoidHom z
  have hz : ∏ w : InfinitePlace C, HarrisDatum.single w (y w) = z := by
    apply Units.ext
    rw [Units.coe_prod]
    change (∏ w : InfinitePlace C, Pi.mulSingle w (z.val w)) = z.val
    exact Finset.univ_prod_mulSingle z.val
  have hψ : ψ.atInfinity z = ∏ w : InfinitePlace C, ψ.infiniteComponent w (y w) := by
    conv_lhs => rw [← hz, map_prod]
    exact Finset.prod_congr rfl fun w _ => (HarrisDatum.infiniteComponent_eq_atInfinity ψ w (y w)).symm
  rw [hψ, Units.coe_prod, ← Finset.prod_mul_distrib, InfinityType.toCharacter_apply, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro w _
  have hy : (y w).val = z.val w := rfl
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_star,
    InfinityType.coordinate_apply, hy] using hlocal w (y w)

omit [IsTotallyComplex A] in
private theorem isConjugateInverse_normComp_comap [IsCMField T] [IsCMField C]
    (e : T ≃+* A) (χ : HeckeCharacter T) (hχ : IsConjugateInverse χ) :
    IsConjugateInverse (HeckeCharacter.normComp (L := C) (HeckeCharacter.comap e.symm χ)) := by
  let c := (IsCMField.complexConj T).toRingEquiv
  let cA := (e.symm.trans c).trans e
  let cC := (IsCMField.complexConj C).toRingEquiv
  have hc : (algebraMap A C).comp cA.toRingHom = cC.toRingHom.comp (algebraMap A C) := by
    apply RingHom.ext
    intro x
    have hx := map_complexConj ((algebraMap A C).comp e.toRingHom) (e.symm x)
    change algebraMap A C (cA x) = cC (algebraMap A C x)
    change algebraMap A C (cA x) = cC (algebraMap A C (e (e.symm x))) at hx
    simpa only [e.apply_symm_apply] using hx
  have hcomm : cA.trans e.symm = e.symm.trans c := by
    apply RingEquiv.ext
    intro x
    exact e.symm_apply_apply (c (e.symm x))
  intro x
  change χ (ideleClassEquiv e.symm (ideleClassNorm (K := A) (ideleClassEquiv cC x))) =
    (χ (ideleClassEquiv e.symm (ideleClassNorm (K := A) x)))⁻¹
  rw [ideleClassNorm_equiv cA cC hc]
  have hy := congrArg (fun e' : A ≃+* T => ideleClassEquiv e' (ideleClassNorm (K := A) x)) hcomm
  simp only [ideleClassEquiv_trans, ContinuousMulEquiv.trans_apply] at hy
  rw [hy]
  exact hχ _

end Character

section Mackey

universe uF

variable (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L)

local notation "A₀" => Q.conjugateField a
local notation "C₀" => Q.mackeyField D a

local instance leftAlgebra : Algebra D C₀ :=
  (IntermediateField.inclusion (show D ≤ C₀ from le_sup_left)).toAlgebra

local instance rightAlgebra : Algebra A₀ C₀ :=
  (IntermediateField.inclusion (show A₀ ≤ C₀ from le_sup_right)).toAlgebra

private def mackeyEmbedding : Q.E' →ₐ[Q.E] C₀ :=
  (IntermediateField.inclusion (show A₀ ≤ C₀ from le_sup_right)).comp
    (Q.conjugateEmbedding a).equivFieldRange.toAlgHom

private theorem mackeyEmbedding_comp :
    (mackeyEmbedding Q D a).toRingHom.comp (algebraMap Q.E Q.E') =
      (algebraMap D C₀).comp (algebraMap Q.E D) := by
  ext x
  change (mackeyEmbedding Q D a (algebraMap Q.E Q.E' x) : Q.L) =
    (algebraMap Q.E C₀ x : Q.L)
  exact congrArg Subtype.val ((mackeyEmbedding Q D a).commutes x)

private theorem mackeyEmbedding_restricted_places_ne
    (v : InfinitePlace D) (w w' : InfinitePlace C₀) [w.LiesOver v] [w'.LiesOver v]
    (hne : w ≠ w') :
    w.comap (mackeyEmbedding Q D a).toRingHom ≠
      w'.comap (mackeyEmbedding Q D a).toRingHom := by
  let f := (mackeyEmbedding Q D a).toRingHom
  let σ := HarrisDatum.lift v w
  let σ' := HarrisDatum.lift v w'
  let ε := v.embedding.comp (algebraMap Q.E D)
  have hE (z : InfinitePlace C₀) [z.LiesOver v] :
      ((HarrisDatum.lift v z).comp f).comp (algebraMap Q.E Q.E') = ε := by
    rw [RingHom.comp_assoc, show f.comp (algebraMap Q.E Q.E') = _ from
      mackeyEmbedding_comp Q D a, ← RingHom.comp_assoc, HarrisDatum.lift_comp]
  intro he
  have hp : InfinitePlace.mk (σ.comp f) = InfinitePlace.mk (σ'.comp f) := by
    rw [← InfinitePlace.comap_mk, ← InfinitePlace.comap_mk, HarrisDatum.mk_lift,
      HarrisDatum.mk_lift]
    exact he
  rcases InfinitePlace.mk_eq_iff.mp hp with h | h
  · let : Algebra Q.E ℂ := ε.toAlgebra
    have hbase (z : InfinitePlace C₀) [z.LiesOver v] (x : Q.E) :
        HarrisDatum.lift v z (algebraMap Q.E C₀ x) = algebraMap Q.E ℂ x :=
      ((congrArg (HarrisDatum.lift v z) ((mackeyEmbedding Q D a).commutes x)).symm.trans
        (RingHom.congr_fun (hE z) x))
    let g : C₀ →ₐ[Q.E] ℂ := { σ with commutes' := hbase w }
    let g' : C₀ →ₐ[Q.E] ℂ := { σ' with commutes' := hbase w' }
    have hg : g = g' := by
      apply IntermediateField.algHom_ext_of_eq_adjoin Q.E (IntermediateField.sup_def D A₀)
      rintro x (hx | hx)
      · exact (RingHom.congr_fun (HarrisDatum.lift_comp v w) ⟨x, hx⟩).trans
          (RingHom.congr_fun (HarrisDatum.lift_comp v w') ⟨x, hx⟩).symm
      · obtain ⟨t, ht⟩ := (Q.conjugateEmbedding a).equivFieldRange.surjective ⟨x, hx⟩
        let j := IntermediateField.inclusion (show A₀ ≤ C₀ from le_sup_right)
        have hft : f t = j ⟨x, hx⟩ := congrArg j ht
        have hgt := RingHom.congr_fun h t
        change g (f t) = g' (f t) at hgt
        rwa [hft] at hgt
    have hσ : σ = σ' := congrArg AlgHom.toRingHom hg
    apply hne
    rw [← HarrisDatum.mk_lift v w, ← HarrisDatum.mk_lift v w']
    exact congrArg InfinitePlace.mk hσ
  · have hconj := congrArg (fun g : Q.E' →+* ℂ => g.comp (algebraMap Q.E Q.E')) h
    rw [HarrisDatum.conjugate_comp, hE w, hE w'] at hconj
    exact HarrisDatum.conjugate_ne ε hconj

private theorem isRelativelyRegular_mackeyCharacter [IsTotallyComplex D] [IsTotallyComplex A₀]
    (hχ : IsRelativelyRegular Q.E Q.ξ) : IsRelativelyRegular D (Q.mackeyCharacter D a) := by
  intro v w w' _ _ hne
  let e : Q.E' ≃+* A₀ := (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv
  let f := (mackeyEmbedding Q D a).toRingHom
  let τ := v.comap (algebraMap Q.E D)
  let : v.LiesOver τ := liesOver_of_comap_eq rfl
  let q (z : InfinitePlace C₀) := z.comap f
  have hq (z : InfinitePlace C₀) [z.LiesOver v] :
      (q z).comap (algebraMap Q.E Q.E') = τ := by
    rw [← InfinitePlace.comap_comp, show f.comp (algebraMap Q.E Q.E') = _ from
      mackeyEmbedding_comp Q D a, InfinitePlace.comap_comp, InfinitePlace.LiesOver.comap_eq z v]
  let : (q w).LiesOver τ := liesOver_of_comap_eq (hq w)
  let : (q w').LiesOver τ := liesOver_of_comap_eq (hq w')
  obtain ⟨x, hx⟩ := hχ τ (q w) (q w') (mackeyEmbedding_restricted_places_ne Q D a v w w' hne)
  let y := Units.map (LiesOver.completionMap (v := τ) (w := v)).toMonoidHom x
  have hcomponent (z : InfinitePlace C₀) [z.LiesOver v] [(q z).LiesOver τ] :
      (Q.mackeyCharacter D a).infiniteComponent z
          (Units.map (LiesOver.completionMap (v := v) (w := z)).toMonoidHom y) =
        Q.ξ.infiniteComponent (q z)
          (Units.map (LiesOver.completionMap (v := τ) (w := q z)).toMonoidHom x) := by
    let r : τ.Completion →+* z.Completion :=
      completedMap (f.comp (algebraMap Q.E Q.E')) τ z (by
        rw [InfinitePlace.comap_comp]
        exact hq z)
    let x' := Units.map (LiesOver.completionMap (v := τ) (w := q z)).toMonoidHom x
    have h1 : (Units.map (LiesOver.completionMap (v := v) (w := z)).toMonoidHom y) =
        Units.map r.toMonoidHom x := by
      apply Units.ext
      change LiesOver.completionMap (LiesOver.completionMap x.val) = r x.val
      rw [← completedMap_algebra v z, ← completedMap_algebra τ v]
      exact RingHom.congr_fun (completedMap_comp (mackeyEmbedding_comp Q D a).symm
        τ v z _ _ _) x.val
    have h2 : (Units.map (completedMap f (q z) z rfl).toMonoidHom x') =
        Units.map r.toMonoidHom x := by
      apply Units.ext
      change completedMap f (q z) z rfl (LiesOver.completionMap x.val) = r x.val
      rw [← completedMap_algebra τ (q z)]
      exact RingHom.congr_fun (completedMap_comp rfl τ (q z) z _ rfl _) x.val
    rw [h1, ← h2]
    exact normComp_comap_component (A := A₀) e Q.ξ z (q z) rfl x'
  exact ⟨y, by rwa [hcomponent w, hcomponent w']⟩

/-- The actual raw Mackey character preserves the prescribed twist, relative regularity,
and conjugate inversion. -/
theorem mackeyCharacter_inherits [IsTotallyComplex D] [IsCMField C₀] (b : ℕ)
    (halg : IsAlgebraicAfterTwist b Q.ξ) (hreg : IsRelativelyRegular Q.E Q.ξ)
    (hconj : IsConjugateInverse Q.ξ) :
    IsAlgebraicAfterTwist b (Q.mackeyCharacter D a) ∧
      IsRelativelyRegular D (Q.mackeyCharacter D a) ∧
      IsConjugateInverse (Q.mackeyCharacter D a) := by
  let e : Q.E' ≃+* A₀ := (Q.conjugateEmbedding a).equivFieldRange.toRingEquiv
  let : IsTotallyComplex A₀ := isTotallyComplex_of_algebra Q.E _
  exact ⟨isAlgebraicAfterTwist_normComp_comap (A := A₀) (C := C₀) e Q.ξ b halg,
    isRelativelyRegular_mackeyCharacter Q D a hreg,
    isConjugateInverse_normComp_comap (A := A₀) (C := C₀) e Q.ξ hconj⟩

end Mackey

end Langlands.Global.Harris
