import Langlands.Global.Arithmetic.HarrisProposition48SpacedData
import Langlands.Global.HeckeCharacterTransport

/-!
# Weights at distance at least two pass to the Mackey children of Proposition 4.8

At each Mackey step of the induction for Harris (1998), Proposition 4.8, the inducing
character of a child is the Mackey character `a(ξ) ∘ N` on the compositum, carried to
the child's fields by isomorphisms. The archimedean weights of the child above a place
of its base field are among those of the parent above the place below, so weights at
distance at least two stay at distance at least two. This module proves it, together
with the passage of even real degree to the child's base field.
-/

noncomputable section

namespace Langlands.Global.Harris

open NumberField InfinitePlace.Completion AdelicFunctoriality
open scoped NumberField.LiesOver

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
  refine eq_onCompletion (continuous_completedMap _ _ _ _) (LiesOver.continuous_completionMap v w)
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

private theorem liesOver_of_comap_eq [Algebra K L] {v : InfinitePlace K}
    {w : InfinitePlace L} (h : w.comap (algebraMap K L) = v) : w.LiesOver v :=
  ⟨by ext x; exact InfinitePlace.comp_of_comap_eq h x⟩

/-- Along a completed map the rotation character is preserved or inverted, according to
the orientation of the two embeddings. -/
private theorem rotation_completedMap [NumberField K] [NumberField L] (f : K →+* L)
    (v : InfinitePlace K) (w : InfinitePlace L) (h : w.comap f = v) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ x : v.Completionˣ,
      rotation L w (Units.map (completedMap f v w h).toMonoidHom x) = rotation K v x ^ ε := by
  rcases embedding_over f v w h with e | e
  · refine ⟨1, Or.inl rfl, fun x => ?_⟩
    have hx := completionEmbedding_of_eq f v w h e (x : v.Completion)
    change extensionEmbedding w (completedMap f v w h x) /
      star (extensionEmbedding w (completedMap f v w h x)) = _
    rw [hx, zpow_one]
    rfl
  · refine ⟨-1, Or.inr rfl, fun x => ?_⟩
    have hx := completionEmbedding_of_conjugate_eq f v w h e (x : v.Completion)
    change extensionEmbedding w (completedMap f v w h x) /
      star (extensionEmbedding w (completedMap f v w h x)) = _
    rw [hx, star_star, zpow_neg, zpow_one, rotation, inv_div]

end Infinite

section Transport

variable {A A' B B' : Type*} [Field A] [NumberField A] [Field A'] [NumberField A']
  [Algebra A A'] [Field B] [NumberField B] [Field B'] [NumberField B'] [Algebra B B']

/-- Weights at distance at least two are transported along compatible isomorphisms of the
base fields and of the top fields. -/
theorem IsRelativelySpaced.comap (e : A ≃+* B) (e' : A' ≃+* B')
    (hc : e'.toRingHom.comp (algebraMap A A') = (algebraMap B B').comp e.toRingHom)
    {χ : HeckeCharacter B'} (h : IsRelativelySpaced B χ) :
    IsRelativelySpaced A (HeckeCharacter.comap e' χ) := by
  intro τ w w' hw hw' hne k hk
  obtain ⟨τB, rfl⟩ := (infinitePlaceEquiv e).surjective τ
  obtain ⟨wB, rfl⟩ := (infinitePlaceEquiv e').surjective w
  obtain ⟨wB', rfl⟩ := (infinitePlaceEquiv e').surjective w'
  have hz (z : InfinitePlace B') [(infinitePlaceEquiv e' z).LiesOver (infinitePlaceEquiv e τB)] :
      z.comap ((algebraMap B B').comp e.toRingHom) = infinitePlaceEquiv e τB := by
    rw [← hc, InfinitePlace.comap_comp]
    exact InfinitePlace.LiesOver.comap_eq (infinitePlaceEquiv e' z) (infinitePlaceEquiv e τB)
  have hB (z : InfinitePlace B') [(infinitePlaceEquiv e' z).LiesOver (infinitePlaceEquiv e τB)] :
      z.comap (algebraMap B B') = τB := by
    apply (infinitePlaceEquiv e).injective
    change (z.comap (algebraMap B B')).comap e.toRingHom = _
    rw [← InfinitePlace.comap_comp]
    exact hz z
  have : wB.LiesOver τB := liesOver_of_comap_eq (hB wB)
  have : wB'.LiesOver τB := liesOver_of_comap_eq (hB wB')
  have hneB : wB ≠ wB' := fun heq => hne (by rw [heq])
  -- The square of completed maps.
  have hsq (z : InfinitePlace B') [(infinitePlaceEquiv e' z).LiesOver (infinitePlaceEquiv e τB)]
      [z.LiesOver τB] (y : (infinitePlaceEquiv e τB).Completion) :
      infiniteCompletionEquiv e' z
          (LiesOver.completionMap (infinitePlaceEquiv e τB) (infinitePlaceEquiv e' z) y) =
        LiesOver.completionMap τB z (infiniteCompletionEquiv e τB y) := by
    have h1 := completedMap_comp hc (infinitePlaceEquiv e τB) (infinitePlaceEquiv e' z) z
      (InfinitePlace.LiesOver.comap_eq _ _) rfl (hz z)
    have h2 := completedMap_comp (f := e.toRingHom) (g := algebraMap B B') rfl
      (infinitePlaceEquiv e τB) τB z rfl (InfinitePlace.LiesOver.comap_eq z τB) (hz z)
    have h3 := congrArg (fun φ => φ y) (h1.trans h2.symm)
    simp only [RingHom.comp_apply, completedMap_algebra] at h3
    exact h3
  obtain ⟨ε, hε, hrot⟩ := rotation_completedMap e.toRingHom (infinitePlaceEquiv e τB) τB rfl
  have hεk : |ε * k| ≤ 1 := by
    rcases hε with rfl | rfl <;> simpa using hk
  obtain ⟨xB, hxB⟩ := h τB wB wB' hneB (ε * k) hεk
  let x : (infinitePlaceEquiv e τB).Completionˣ :=
    Units.map (infiniteCompletionEquiv e τB).symm.toRingHom.toMonoidHom xB
  have hx : Units.map (completedMap e.toRingHom (infinitePlaceEquiv e τB) τB rfl).toMonoidHom x =
      xB := by
    apply Units.ext
    exact (infiniteCompletionEquiv e τB).apply_symm_apply (xB : τB.Completion)
  refine ⟨x, fun heq => hxB ?_⟩
  have hcomp (z : InfinitePlace B') [(infinitePlaceEquiv e' z).LiesOver (infinitePlaceEquiv e τB)]
      [z.LiesOver τB] :
      (HeckeCharacter.comap e' χ).infiniteComponent (infinitePlaceEquiv e' z)
          (Units.map (LiesOver.completionMap (v := infinitePlaceEquiv e τB)
            (w := infinitePlaceEquiv e' z)).toMonoidHom x) =
        χ.infiniteComponent z (Units.map (LiesOver.completionMap (v := τB) (w := z)).toMonoidHom xB) := by
    rw [HeckeCharacter.comap_infiniteComponent]
    congr 1
    apply Units.ext
    rw [← hx]
    exact hsq z _
  rw [hcomp wB, hcomp wB'] at heq
  rw [heq, ← hx, hrot x, ← zpow_mul, ← mul_assoc]
  rcases hε with rfl | rfl <;> simp

end Transport

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
    change InfiniteExtension.localNorm p w (LiesOver.completionMap p w y.val) = y.val
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

end Character

section Mackey

universe uF

variable (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L)

local notation "A₀" => Q.conjugateField a
local notation "C₀" => Q.mackeyField D a

private local instance leftAlgebra : Algebra D C₀ :=
  (IntermediateField.inclusion (show D ≤ C₀ from le_sup_left)).toAlgebra

private local instance rightAlgebra : Algebra A₀ C₀ :=
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

/-- The Mackey character keeps the weights at distance at least two: its archimedean
components at the places of `D · a(E')` above a place of `D` are those of `ξ` at distinct
places of `E'` above the place of `E` below. -/
theorem isRelativelySpaced_mackeyCharacter [IsTotallyComplex D] [IsTotallyComplex A₀]
    (hχ : IsRelativelySpaced Q.E Q.ξ) : IsRelativelySpaced D (Q.mackeyCharacter D a) := by
  intro v w w' _ _ hne k hk
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
  obtain ⟨ε, hε, hrot⟩ := rotation_completedMap (algebraMap Q.E D) τ v
    (InfinitePlace.LiesOver.comap_eq v τ)
  have hεk : |ε * k| ≤ 1 := by
    rcases hε with rfl | rfl <;> simpa using hk
  obtain ⟨x, hx⟩ := hχ τ (q w) (q w')
    (mackeyEmbedding_restricted_places_ne Q D a v w w' hne) (ε * k) hεk
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
      change LiesOver.completionMap v z (LiesOver.completionMap τ v x.val) = r x.val
      rw [← completedMap_algebra v z, ← completedMap_algebra τ v]
      exact RingHom.congr_fun (completedMap_comp (mackeyEmbedding_comp Q D a).symm
        τ v z _ _ _) x.val
    have h2 : (Units.map (completedMap f (q z) z rfl).toMonoidHom x') =
        Units.map r.toMonoidHom x := by
      apply Units.ext
      change completedMap f (q z) z rfl (LiesOver.completionMap τ (q z) x.val) = r x.val
      rw [← completedMap_algebra τ (q z)]
      exact RingHom.congr_fun (completedMap_comp rfl τ (q z) z _ rfl _) x.val
    rw [h1, ← h2]
    exact normComp_comap_component (A := A₀) e Q.ξ z (q z) rfl x'
  have hy : rotation D v y = rotation Q.E τ x ^ ε := by
    rw [← hrot x]
    congr 1
  refine ⟨y, fun heq => hx ?_⟩
  rw [hcomponent w, hcomponent w', hy, ← zpow_mul] at heq
  exact heq

/-- The Mackey children of the induction keep both clauses. The child's base field is a
copy of `D ⊇ E`, so its real degree is even with that of `E`; the child's character is
the Mackey character carried by the child's isomorphisms, which keeps the weights at
distance at least two (`isRelativelySpaced_mackeyCharacter`, `IsRelativelySpaced.comap`). -/
theorem _root_.Langlands.Global.Harris.Proposition48Problem.IsSpaced.of_auxiliaryMackeyChild
    {R : Proposition48Problem.{uF}} (hQ : Q.IsSpaced) (hR : Q.IsAuxiliaryMackeyChild D a R) :
    R.IsSpaced := by
  obtain ⟨e₀, e₀', -, -, he₀, -, -, hξ₀, -, -⟩ := hR
  let e : R.E ≃+* D := e₀
  let e' : R.E' ≃+* C₀ := e₀'
  have he : ∀ x : R.E, (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L) := he₀
  have hξ : R.ξ = HeckeCharacter.comap e' (Q.mackeyCharacter D a) := hξ₀
  have : IsTotallyComplex D := isTotallyComplex_of_algebra Q.E _
  have : IsTotallyComplex A₀ := isTotallyComplex_of_algebra Q.E _
  refine ⟨?_, ?_⟩
  · have hE := hQ.1
    rw [hasEvenRealDegree_iff] at hE ⊢
    rw [(e.toRatAlgEquiv).toLinearEquiv.finrank_eq, ← Module.finrank_mul_finrank ℚ Q.E D]
    exact Dvd.dvd.mul_right hE _
  · have hM := isRelativelySpaced_mackeyCharacter Q D a hQ.2
    have hc : e'.toRingHom.comp (algebraMap R.E R.E') = (algebraMap D C₀).comp e.toRingHom :=
      RingHom.ext fun x => Subtype.ext (he x)
    change IsRelativelySpaced R.E R.ξ
    rw [hξ]
    exact hM.comap e e' hc

end Mackey

end Langlands.Global.Harris
