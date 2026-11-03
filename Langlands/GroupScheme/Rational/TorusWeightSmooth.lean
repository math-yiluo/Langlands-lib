import Langlands.GroupScheme.Rational.TorusWeightSubgroups
import Mathlib.RingTheory.Smooth.Basic

/-! # Formal smoothness of weight subgroups with positive weights -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

section Coefficients

variable {Λ A : Type*} [AddCommGroup Λ] [CommRing A]

/-- A coefficient of a product is the product of two coefficients when all other
contributions vanish. -/
theorem coeff_mul_add_eq {x y : AddMonoidAlgebra A Λ} {m m' : Λ}
    (h : ∀ i j, i + j = m + m' → i ≠ m → x.coeff i * y.coeff j = 0) :
    (x * y).coeff (m + m') = x.coeff m * y.coeff m' := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum, Finset.sum_eq_single m]
  · rw [neg_add_cancel_left]
  · intro i _ hi
    exact h i _ (add_neg_cancel_left i (m + m')) hi
  · intro hm
    rw [Finsupp.notMem_support_iff.mp hm, zero_mul]

variable {N : Ideal A}

theorem mul_eq_zero_of_mem (hN : N ^ 2 = ⊥) {a b : A} (ha : a ∈ N) (hb : b ∈ N) :
    a * b = 0 := by
  have h : a * b ∈ N ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul ha hb
  rwa [hN, Ideal.mem_bot] at h

/-- The product of two elements with all coefficients in a square-zero ideal vanishes. -/
theorem mul_eq_zero_of_forall_coeff_mem (hN : N ^ 2 = ⊥) {x y : AddMonoidAlgebra A Λ}
    (hx : ∀ i, x.coeff i ∈ N) (hy : ∀ j, y.coeff j ∈ N) : x * y = 0 := by
  apply AddMonoidAlgebra.coeff_injective
  ext k
  rw [AddMonoidAlgebra.coeff_mul_apply_left, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    Finsupp.sum]
  exact Finset.sum_eq_zero fun i _ => mul_eq_zero_of_mem hN (hx i) (hy _)

/-- The constant coefficient is multiplicative on elements whose other coefficients lie in a
square-zero ideal. -/
theorem coeff_zero_mul_of_mem (hN : N ^ 2 = ⊥) {x y : AddMonoidAlgebra A Λ}
    (hx : ∀ i ≠ 0, x.coeff i ∈ N) (hy : ∀ j ≠ 0, y.coeff j ∈ N) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  have h := coeff_mul_add_eq (x := x) (y := y) (m := 0) (m' := 0) fun i j hij hi => by
    have hj : j ≠ 0 := by
      rintro rfl
      rw [add_zero, add_zero] at hij
      exact hi hij
    exact mul_eq_zero_of_mem hN (hx i hi) (hy j hj)
  rwa [add_zero] at h

/-- The constant coefficient is multiplicative on elements supported on a semigroup not
containing zero, together with zero. -/
theorem coeff_zero_mul_of_supported {P : AddSubsemigroup Λ} (h0 : (0 : Λ) ∉ P)
    {x y : AddMonoidAlgebra A Λ} (hx : ∀ i ∉ insertZero P, x.coeff i = 0)
    (hy : ∀ j ∉ insertZero P, y.coeff j = 0) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  have h := coeff_mul_add_eq (x := x) (y := y) (m := 0) (m' := 0) fun i j hij hi => by
    rw [add_zero] at hij
    by_cases hxi : x.coeff i = 0
    · rw [hxi, zero_mul]
    by_cases hyj : y.coeff j = 0
    · rw [hyj, mul_zero]
    exfalso
    rcases (mem_insertZero P i).1 (by_contra fun h => hxi (hx i h)) with hi' | hi'
    · exact hi hi'
    rcases (mem_insertZero P j).1 (by_contra fun h => hyj (hy j h)) with hj' | hj'
    · rw [hj', add_zero] at hij
      exact hi hij
    · exact h0 (by rw [← hij]; exact P.add_mem hi' hj')
  rwa [add_zero] at h

/-- The constant coefficient of an algebra map into a group algebra, when it is
multiplicative. -/
def coeffZeroHom {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] [Algebra S A]
    (φ : T →ₐ[S] AddMonoidAlgebra A Λ)
    (h : ∀ f g, (φ f * φ g).coeff 0 = (φ f).coeff 0 * (φ g).coeff 0) : T →ₐ[S] A where
  toFun f := (φ f).coeff 0
  map_one' := by
    rw [map_one, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  map_mul' f g := by rw [map_mul, h]
  map_zero' := by
    change (φ 0).coeff 0 = 0
    rw [show φ 0 = 0 from map_zero φ]
    rfl
  map_add' f g := by
    change (φ (f + g)).coeff 0 = (φ f).coeff 0 + (φ g).coeff 0
    rw [show φ (f + g) = φ f + φ g from map_add φ f g]
    rfl
  commutes' r := by
    rw [AlgHom.commutes, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

theorem coeffZeroHom_apply {S T : Type*} [CommRing S] [CommRing T] [Algebra S T] [Algebra S A]
    (φ : T →ₐ[S] AddMonoidAlgebra A Λ)
    (h : ∀ f g, (φ f * φ g).coeff 0 = (φ f).coeff 0 * (φ g).coeff 0) (f : T) :
    coeffZeroHom φ h f = (φ f).coeff 0 :=
  rfl

end Coefficients

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section SupportedMap

variable {I : Type u}

/-- Coefficientwise application of an algebra map to supported elements. -/
def supportedMap (M : AddSubmonoid (I → ℤ)) {A A' : CommAlgCat.{u} R} (g : A →ₐ[R] A') :
    supportedSubalgebra I A M →ₐ[R] supportedSubalgebra I A' M :=
  ((AddMonoidAlgebra.mapAlgHom (I → ℤ) g).comp (supportedSubalgebra I A M).val).codRestrict _
    fun s m hm => by
      change (AddMonoidAlgebra.mapAlgHom (I → ℤ) g (s : AddMonoidAlgebra A (I → ℤ))).coeff m = 0
      rw [AddMonoidAlgebra.coeff_mapAlgHom, s.2 m hm, map_zero]

theorem coeff_supportedMap (M : AddSubmonoid (I → ℤ)) {A A' : CommAlgCat.{u} R}
    (g : A →ₐ[R] A') (s : supportedSubalgebra I A M) (m : I → ℤ) :
    ((supportedMap M g s : laurent I A') : AddMonoidAlgebra A' (I → ℤ)).coeff m =
      g ((s : AddMonoidAlgebra A (I → ℤ)).coeff m) :=
  AddMonoidAlgebra.coeff_mapAlgHom _ _ _

theorem supportedMap_surjective (M : AddSubmonoid (I → ℤ)) {A A' : CommAlgCat.{u} R}
    {g : A →ₐ[R] A'} (hg : Function.Surjective g) : Function.Surjective (supportedMap M g) := by
  classical
  intro s
  let l : A' → A := fun c => if c = 0 then 0 else Function.surjInv hg c
  have hl : ∀ c, g (l c) = c := by
    intro c
    by_cases hc : c = 0
    · simp [l, hc]
    · simp only [l, hc]
      simpa using Function.surjInv_eq hg c
  have l0 : l 0 = 0 := by simp [l]
  refine ⟨⟨AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange l l0 (s : AddMonoidAlgebra A' (I → ℤ)).coeff), fun m hm => ?_⟩, ?_⟩
  · change Finsupp.mapRange l l0 (s : AddMonoidAlgebra A' (I → ℤ)).coeff m = 0
    rw [Finsupp.mapRange_apply, s.2 m hm, l0]
  · apply Subtype.ext
    apply AddMonoidAlgebra.coeff_injective
    ext m
    rw [coeff_supportedMap]
    change g (Finsupp.mapRange l l0 (s : AddMonoidAlgebra A' (I → ℤ)).coeff m) = _
    rw [Finsupp.mapRange_apply, hl]

theorem coeff_mem_of_supportedMap_eq_zero (M : AddSubmonoid (I → ℤ)) {A : CommAlgCat.{u} R}
    (N : Ideal A) {s : supportedSubalgebra I A M}
    (hs : supportedMap (A' := CommAlgCat.of R (A ⧸ N)) M (Ideal.Quotient.mkₐ R N) s = 0)
    (i : I → ℤ) : ((s : laurent I A) : AddMonoidAlgebra A (I → ℤ)).coeff i ∈ N := by
  have h := coeff_supportedMap (A' := CommAlgCat.of R (A ⧸ N)) M (Ideal.Quotient.mkₐ R N) s i
  rw [hs] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h.symm

/-- The kernel of coefficientwise reduction modulo a square-zero ideal is square-zero. -/
theorem supportedMap_ker_sq (M : AddSubmonoid (I → ℤ)) {A : CommAlgCat.{u} R} (N : Ideal A)
    (hN : N ^ 2 = ⊥) :
    RingHom.ker (supportedMap (A' := CommAlgCat.of R (A ⧸ N)) M (Ideal.Quotient.mkₐ R N)) ^ 2 =
      ⊥ := by
  rw [sq, eq_bot_iff, Ideal.mul_le]
  intro s hs t ht
  rw [Ideal.mem_bot]
  apply Subtype.ext
  exact mul_eq_zero_of_forall_coeff_mem hN
    (coeff_mem_of_supportedMap_eq_zero M N (RingHom.mem_ker.mp hs))
    (coeff_mem_of_supportedMap_eq_zero M N (RingHom.mem_ker.mp ht))

end SupportedMap

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

theorem coord_hat_mem_supportedSubalgebra (M : AddSubmonoid (I → ℤ)) {A : CommAlgCat.{u} R}
    {x : F.obj A} (h : ∀ f m, m ∉ M → coord e x (comp e σ m f) = 0) (f : B) :
    coord e (hat σ x) f ∈ supportedSubalgebra I A M := by
  intro m hm
  rw [coord_hat_coeff, h f m hm]

theorem coord_comp_eq_zero_of_mem_weightSubgroup {P : AddSubsemigroup (I → ℤ)}
    {A : CommAlgCat.{u} R} {x : F.obj A} (hx : x ∈ weightSubgroup e σ P A) (f : B)
    {m : I → ℤ} (hm : m ∉ insertZero P) : coord e x (comp e σ m f) = 0 := by
  have hm0 : m ≠ 0 := fun h => hm ((mem_insertZero P m).2 (Or.inl h))
  have hmP : m ∉ P := fun h => hm ((mem_insertZero P m).2 (Or.inr h))
  rw [(mem_weightSubgroup e σ P x).1 hx f m hmP, counit_comp]
  simp [hm0]

omit [DecidableEq I] in
theorem exponentValue_inv {A : Type u} [CommRing A] (t : I → Aˣ) (m : I → ℤ) :
    splitTorus.exponentValue I t⁻¹ (Multiplicative.ofAdd m) =
      splitTorus.exponentValue I t (Multiplicative.ofAdd (-m)) := by
  change ∏ i, (t i)⁻¹ ^ m i = ∏ i, t i ^ (-m) i
  simp only [inv_zpow', Pi.neg_apply]

/-- Coefficientwise application of a morphism to group algebras. -/
abbrev laurentMap {A A' : CommAlgCat.{u} R} (g : A ⟶ A') : laurent I A ⟶ laurent I A' :=
  CommAlgCat.ofHom (AddMonoidAlgebra.mapAlgHom (I → ℤ) g.hom)

omit [Fintype I] in
theorem units_map_laurentMap {A A' : CommAlgCat.{u} R} (g : A ⟶ A') :
    (fun i => Units.map (laurentMap (I := I) g).hom.toMonoidHom ((universalUnits I A)⁻¹ i)) =
      (universalUnits I A')⁻¹ := by
  funext i
  rw [Pi.inv_apply, Pi.inv_apply, map_inv]
  congr 1
  apply Units.ext
  change AddMonoidAlgebra.mapAlgHom (I → ℤ) g.hom (AddMonoidAlgebra.single (Pi.single i 1) 1) =
    AddMonoidAlgebra.single (Pi.single i 1) 1
  rw [AddMonoidAlgebra.mapAlgHom_single, map_one]

variable [Algebra.FormallySmooth R B]

/-- Points of a weight subgroup with weights in a semigroup not containing zero lift along
square-zero thickenings. -/
theorem exists_lift_mem_weightSubgroup (P : AddSubsemigroup (I → ℤ)) (h0 : (0 : I → ℤ) ∉ P)
    {C : CommAlgCat.{u} R} (N : Ideal C) (hN : N ^ 2 = ⊥)
    {u₀ : F.obj (CommAlgCat.of R (C ⧸ N))}
    (hu₀ : u₀ ∈ weightSubgroup e σ P (CommAlgCat.of R (C ⧸ N))) :
    ∃ u ∈ weightSubgroup e σ P C, F.map (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)) u = u₀ := by
  let Q := CommAlgCat.of R (C ⧸ N)
  let M := insertZero P
  let π : C ⟶ Q := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)
  have hπ : ∀ c, π.hom c = 0 ↔ c ∈ N := fun c => Ideal.Quotient.eq_zero_iff_mem
  -- Step 1: lift the twisted point with supported coordinates.
  let φ₀ : B →ₐ[R] supportedSubalgebra I Q M :=
    (coord e (hat σ u₀)).codRestrict _ (coord_hat_mem_supportedSubalgebra e σ M
      fun f _ hm => coord_comp_eq_zero_of_mem_weightSubgroup e σ hu₀ f hm)
  let φ : B →ₐ[R] supportedSubalgebra I C M :=
    Algebra.FormallySmooth.liftOfSurjective φ₀ (supportedMap M π.hom)
      (supportedMap_surjective M Ideal.Quotient.mk_surjective)
      ⟨2, by rw [Ideal.zero_eq_bot]; exact supportedMap_ker_sq M N hN⟩
  have hφ : ∀ f, supportedMap M π.hom (φ f) = φ₀ f :=
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _
  let X : F.obj (laurent I C) := ofCoord e ((supportedSubalgebra I C M).val.comp φ)
  have hX : F.map (laurentMap π) X = hat σ u₀ := by
    apply coord_injective e
    rw [coord_map, coord_ofCoord]
    apply AlgHom.ext
    intro f
    exact congrArg Subtype.val (hφ f)
  have hXs : ∀ f m, m ∉ M → (coord e X f).coeff m = 0 := by
    intro f m hm
    rw [coord_ofCoord]
    exact (φ f).2 m hm
  -- Step 2: untwist by the inverse universal units.
  let Y : F.obj (laurent I C) := σ.act (universalUnits I C)⁻¹ X
  have hY : F.map (laurentMap π) Y = F.map (constHom I Q) u₀ := by
    change F.map (laurentMap π) (σ.act _ X) = _
    rw [σ.naturality, units_map_laurentMap, hX]
    change σ.act (A := laurent I Q) (universalUnits I Q)⁻¹
      (σ.act (A := laurent I Q) (universalUnits I Q) (F.map (constHom I Q) u₀)) = _
    rw [← σ.act_mul, inv_mul_cancel, σ.act_one]
  have hYc : ∀ f, AddMonoidAlgebra.mapAlgHom (I → ℤ) π.hom (coord e Y f) =
      AddMonoidAlgebra.single 0 (coord e u₀ f) := by
    intro f
    have h := congrArg (fun y => coord e y f) hY
    simp only [coord_map, AlgHom.comp_apply] at h
    exact h
  have hYN : ∀ f n, n ≠ 0 → (coord e Y f).coeff n ∈ N := by
    intro f n hn
    rw [← hπ]
    have h := congrArg (fun s => AddMonoidAlgebra.coeff s n) (hYc f)
    simp only at h
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_of_ne hn] at h
    exact h
  have hYh : ∀ m h, IsHomogeneous e σ m h →
      coord e Y h = coord e X h * AddMonoidAlgebra.single (-m) 1 := by
    intro m h hh
    change coord e (σ.act _ X) h = _
    rw [coord_act_of_isHomogeneous e σ _ X hh, exponentValue_inv, exponentValue_universalUnits]
    rfl
  -- Step 3: the constant coefficient of the untwisted point.
  let p : B →ₐ[R] C := coeffZeroHom (coord e Y) fun f g =>
    coeff_zero_mul_of_mem hN (hYN f) (hYN g)
  let v : F.obj C := ofCoord e p
  have hv : F.map π v = u₀ := by
    apply coord_injective e
    rw [coord_map, coord_ofCoord]
    apply AlgHom.ext
    intro f
    change π.hom ((coord e Y f).coeff 0) = coord e u₀ f
    have h := congrArg (fun s => AddMonoidAlgebra.coeff s 0) (hYc f)
    simp only at h
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same] at h
    exact h
  have hvM : ∀ f m, m ∉ M → coord e v (comp e σ m f) = 0 := by
    intro f m hm
    rw [coord_ofCoord, coeffZeroHom_apply, hYh m _ (isHomogeneous_comp e σ m f)]
    have h0m : (0 : I → ℤ) = m + -m := (add_neg_cancel m).symm
    rw [h0m, AddMonoidAlgebra.coeff_mul_single_add, hXs _ m hm, zero_mul]
  have hvS : ∀ f, ∀ i ∉ insertZero P, (coord e (hat σ v) f).coeff i = 0 := by
    intro f i hi
    rw [coord_hat_coeff]
    exact hvM f i hi
  -- Step 4: correct the weight-zero part.
  let z : B →ₐ[R] C := coeffZeroHom (coord e (hat σ v)) fun f g =>
    coeff_zero_mul_of_supported h0 (hvS f) (hvS g)
  let w : F.obj C := ofCoord e z
  have hw : ∀ f, coord e w f = coord e v (comp e σ 0 f) := by
    intro f
    rw [coord_ofCoord, coeffZeroHom_apply, coord_hat_coeff]
  have hw' : ∀ f m, coord e w (comp e σ m f) = if m = 0 then coord e v (comp e σ 0 f) else 0 := by
    intro f m
    rw [hw, comp_comp]
    by_cases hm : m = 0
    · subst hm
      simp
    · simp [hm, Ne.symm hm]
  have hwS : ∀ f, coord e (hat σ w) f ∈ supportedSubalgebra I C M :=
    coord_hat_mem_supportedSubalgebra e σ M fun f m hm => by
      have hm0 : m ≠ 0 := fun h => hm ((mem_insertZero P m).2 (Or.inl h))
      rw [hw']
      simp [hm0]
  have hvS' : ∀ f, coord e (hat σ v) f ∈ supportedSubalgebra I C M :=
    coord_hat_mem_supportedSubalgebra e σ M fun f m hm => hvM f m hm
  refine ⟨w⁻¹ * v, ?_, ?_⟩
  · refine (weightCondition_iff e σ (P : Set (I → ℤ)) M (Set.subset_insert _ _)
      (insertZero_add_mem P) _).2 ?_
    rw [map_mul, map_inv]
    refine inv_mul_mem_kerSubgroup e _ _ (g := (coord e (hat σ w)).codRestrict _ hwS)
      (g' := (coord e (hat σ v)).codRestrict _ hvS') (AlgHom.val_comp_codRestrict _ _ _)
      (AlgHom.val_comp_codRestrict _ _ _) fun f m hm => ?_
    change (coord e (hat σ w) f - coord e (hat σ v) f).coeff m = 0
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coord_hat_coeff, coord_hat_coeff,
      sub_eq_zero, hw']
    by_cases hm0 : m = 0
    · subst hm0
      simp
    · have hmM : m ∉ M := fun h => ((mem_insertZero P m).1 h).elim hm0 hm
      rw [hvM f m hmM]
      simp [hm0]
  · have hw1 : F.map π w = 1 := by
      refine (eq_one_iff e).2 fun f => ?_
      rw [coord_map, AlgHom.comp_apply, hw]
      have h := congrArg (fun y => coord e y (comp e σ 0 f)) hv
      simp only [coord_map, AlgHom.comp_apply] at h
      rw [h, (mem_weightSubgroup e σ P u₀).1 hu₀ f 0 h0, counit_comp]
      simp only [↓reduceIte]
      rfl
    change F.map π (w⁻¹ * v) = u₀
    rw [map_mul, map_inv, hw1, hv, inv_one, one_mul]

/-- The quotient of a formally smooth representing algebra by the weight ideal of a semigroup
not containing zero is formally smooth. -/
theorem formallySmooth_quotient_weightIdeal (P : AddSubsemigroup (I → ℤ))
    (h0 : (0 : I → ℤ) ∉ P) : Algebra.FormallySmooth R (B ⧸ weightIdeal e σ P) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ N hN f₀ => ?_
  let u₀ : F.obj (CommAlgCat.of R (C ⧸ N)) :=
    ofCoord e (f₀.comp (Ideal.Quotient.mkₐ R (weightIdeal e σ P)))
  have hu₀c : coord e u₀ = f₀.comp (Ideal.Quotient.mkₐ R (weightIdeal e σ P)) :=
    coord_ofCoord e _
  have hu₀ : u₀ ∈ weightSubgroup e σ P (CommAlgCat.of R (C ⧸ N)) := by
    refine (isCutOutBy_weightIdeal e σ P _ u₀).2 fun b hb => ?_
    change coord e u₀ b = 0
    rw [hu₀c, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
  obtain ⟨u, hu, hmap⟩ :=
    exists_lift_mem_weightSubgroup e σ P h0 (C := CommAlgCat.of R C) N hN hu₀
  refine ⟨Ideal.Quotient.liftₐ _ (coord e u) ((isCutOutBy_weightIdeal e σ P _ u).1 hu), ?_⟩
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro b
  have h := congrArg (fun y => coord e y b) hmap
  simp only [coord_map, AlgHom.comp_apply] at h
  change Ideal.Quotient.mkₐ R N (coord e u b) =
    (f₀.comp (Ideal.Quotient.mkₐ R (weightIdeal e σ P))) b
  rw [← hu₀c]
  exact h

end Langlands.GroupScheme.Corepresented
