import Langlands.AlgebraicGeometry.AlgebraicSpace.SpecFieldPoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorImages
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationStatements
import Langlands.AlgebraicGeometry.AlgebraicSpace.LFTAffineOpen
import Langlands.AlgebraicGeometry.Morphisms.FiniteFlatSourceDescent

/-! # Descent of invariant affine opens along a finite field extension

Let `L/k` be a finite field extension and `F` an fppf sheaf on schemes over `Spec k`. An
affine open subfunctor `W` of `F × Spec L` that is invariant along the projection to `F`
descends: its universal image in `F` is an affine open subfunctor whose preimage is `W`.
The affine quotient comes from the finite locally free equivalence relation
`W ×_k Spec L ⇉ W` and the affine quotient statement of Stacks Proposition 39.23.9 (03BM).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open OpenSubfunctorLifting AffineOpenSubfunctors

variable {k : Type u} [Field k]

section Core

variable {F : Presheaf (Spec (CommRingCat.of k))} {Λ A : Over (Spec (CommRingCat.of k))}

/-- The scheme part of the descent. Let `x₀ ∈ F(A)` and `α₀ : A ⟶ Λ` be such that a test
point of `A` is determined by its two images, and every pair `(F.map a x₀, β)` comes from
a test point of `A`. If `Λ ⟶ Spec k` is finite, flat and of finite presentation and `A` is
affine, then the relation "same image in `F`" is the kernel pair of a finite flat finitely
presented surjection onto an affine scheme over `Spec k`. -/
theorem exists_affine_quotient
    (h03BM : FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u})
    [IsAffine A.left] [_root_.AlgebraicGeometry.IsFinite Λ.hom] [Flat Λ.hom]
    [LocallyOfFinitePresentation Λ.hom]
    (x₀ : F.obj (op A)) (α₀ : A ⟶ Λ)
    (inj : ∀ (T : Over (Spec (CommRingCat.of k))) (a a' : T ⟶ A),
      F.map a.op x₀ = F.map a'.op x₀ → a ≫ α₀ = a' ≫ α₀ → a = a')
    (lift : ∀ (T : Over (Spec (CommRingCat.of k))) (a : T ⟶ A) (β : T ⟶ Λ),
      ∃ a' : T ⟶ A, F.map a'.op x₀ = F.map a.op x₀ ∧ a' ≫ α₀ = β) :
    ∃ (M : Over (Spec (CommRingCat.of k))) (q : A ⟶ M), IsAffine M.left ∧
      _root_.AlgebraicGeometry.IsFinite q.left ∧
      Flat q.left ∧ LocallyOfFinitePresentation q.left ∧ Surjective q.left ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (a a' : T ⟶ A),
        (F.map a.op x₀ = F.map a'.op x₀ ↔ a ≫ q = a' ≫ q) := by
  let R := A ⨯ Λ
  let s : R ⟶ A := prod.fst
  let π₂ : R ⟶ Λ := prod.snd
  obtain ⟨t, hE2, hE1⟩ := lift R s π₂
  have char : ∀ {T : Over (Spec (CommRingCat.of k))} (r : T ⟶ R),
      F.map (r ≫ t).op x₀ = F.map (r ≫ s).op x₀ := by
    intro T r
    rw [op_comp, op_comp, F.map_comp, F.map_comp]
    exact congrArg (F.map r.op) hE2
  have kerOver : ∀ {T : Over (Spec (CommRingCat.of k))} (a a' : T ⟶ A),
      F.map a.op x₀ = F.map a'.op x₀ ↔ ∃ r : T ⟶ R, r ≫ t = a ∧ r ≫ s = a' := by
    intro T a a'
    constructor
    · intro h
      refine ⟨prod.lift a' (a ≫ α₀), ?_, prod.lift_fst _ _⟩
      apply inj
      · rw [char, prod.lift_fst, h]
      · rw [Category.assoc, hE1, prod.lift_snd]
    · rintro ⟨r, rfl, rfl⟩
      exact char r
  let swap : R ⟶ R := prod.lift t (s ≫ α₀)
  have hswap_s : swap ≫ s = t := prod.lift_fst _ _
  have hswap_t : swap ≫ t = s := by
    apply inj
    · rw [char, hswap_s]
      exact hE2
    · rw [Category.assoc, hE1]
      exact prod.lift_snd _ _
  have hswap : swap ≫ swap = 𝟙 R := by
    apply prod.hom_ext
    · rw [Category.assoc, hswap_s, hswap_t, Category.id_comp]
    · rw [Category.assoc, prod.lift_snd, ← Category.assoc, hswap_s, hE1, Category.id_comp]
  have : IsIso swap := ⟨⟨swap, hswap, hswap⟩⟩
  have hts : t.left = swap.left ≫ s.left := by rw [← Over.comp_left, hswap_s]
  -- the absolute equivalence relation
  have hRt : t.left ≫ A.hom = R.hom := Over.w t
  have hRs : s.left ≫ A.hom = R.hom := Over.w s
  have hmono : Mono (prod.lift t.left s.left) := by
    constructor
    intro Z g h hgh
    have h1 : g ≫ t.left = h ≫ t.left := by simpa using congrArg (· ≫ prod.fst) hgh
    have h2 : g ≫ s.left = h ≫ s.left := by simpa using congrArg (· ≫ prod.snd) hgh
    apply extProd.prod_left_hom_ext h2
    have hE1' : π₂.left = t.left ≫ α₀.left := by rw [← Over.comp_left, hE1]
    change g ≫ π₂.left = h ≫ π₂.left
    rw [hE1', ← Category.assoc, h1, Category.assoc]
  have hrefl : ∀ (T : Scheme.{u}) (a : T ⟶ A.left), ∃ r : T ⟶ R.left,
      r ≫ t.left = a ∧ r ≫ s.left = a := by
    intro T a
    obtain ⟨r, hr1, hr2⟩ := (kerOver (T := Over.mk (a ≫ A.hom)) (Over.homMk a)
      (Over.homMk a)).mp rfl
    exact ⟨r.left, by rw [← Over.comp_left, hr1]; rfl, by rw [← Over.comp_left, hr2]; rfl⟩
  have hsymm : ∀ (T : Scheme.{u}) (r : T ⟶ R.left), ∃ r' : T ⟶ R.left,
      r' ≫ t.left = r ≫ s.left ∧ r' ≫ s.left = r ≫ t.left := by
    intro T r
    refine ⟨r ≫ swap.left, ?_, ?_⟩
    · rw [Category.assoc, ← Over.comp_left, hswap_t]
    · rw [Category.assoc, ← Over.comp_left, hswap_s]
  have htrans : ∀ (T : Scheme.{u}) (r r' : T ⟶ R.left), r ≫ s.left = r' ≫ t.left →
      ∃ r'' : T ⟶ R.left, r'' ≫ t.left = r ≫ t.left ∧ r'' ≫ s.left = r' ≫ s.left := by
    intro T r r' hrr
    let T' : Over (Spec (CommRingCat.of k)) := Over.mk (r' ≫ R.hom)
    have hw : r ≫ R.hom = r' ≫ R.hom := by
      calc r ≫ R.hom = r ≫ s.left ≫ A.hom := by rw [hRs]
        _ = r' ≫ t.left ≫ A.hom := by rw [← Category.assoc, hrr, Category.assoc]
        _ = r' ≫ R.hom := by rw [hRt]
    let ro : T' ⟶ R := Over.homMk r hw
    let r'o : T' ⟶ R := Over.homMk r'
    have hcomp : ro ≫ s = r'o ≫ t := Over.OverMorphism.ext hrr
    have hx : F.map (ro ≫ t).op x₀ = F.map (r'o ≫ s).op x₀ := by
      rw [char, hcomp, char]
    obtain ⟨r'', hr1, hr2⟩ := (kerOver (ro ≫ t) (r'o ≫ s)).mp hx
    exact ⟨r''.left, by rw [← Over.comp_left, hr1]; rfl, by rw [← Over.comp_left, hr2]; rfl⟩
  have hsF : _root_.AlgebraicGeometry.IsFinite s.left :=
    extProd.prod_fst_left (@_root_.AlgebraicGeometry.IsFinite) inferInstance
  have hsFl : Flat s.left := extProd.prod_fst_left (@Flat) inferInstance
  have hsL : LocallyOfFinitePresentation s.left :=
    extProd.prod_fst_left (@LocallyOfFinitePresentation) inferInstance
  have : IsIso swap.left := inferInstanceAs (IsIso ((Over.forget _).map swap))
  have htF : _root_.AlgebraicGeometry.IsFinite t.left := by rw [hts]; infer_instance
  have htFl : Flat t.left := by rw [hts]; infer_instance
  have htL : LocallyOfFinitePresentation t.left := by rw [hts]; infer_instance
  obtain ⟨M, q, hM, hpb, hqF, hqFl, hqL, hqS⟩ := h03BM A.left R.left t.left s.left hmono hrefl
    hsymm htrans htF htFl htL hsF hsFl hsL inferInstance
  have : EffectiveEpi q := inferInstance
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ A.left), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ A.hom = g₂ ≫ A.hom := by
    intro Z g₁ g₂ h
    have h1 := hpb.lift_fst g₁ g₂ h
    have h2 := hpb.lift_snd g₁ g₂ h
    calc g₁ ≫ A.hom = (hpb.lift g₁ g₂ h ≫ t.left) ≫ A.hom := by rw [h1]
      _ = hpb.lift g₁ g₂ h ≫ R.hom := by rw [Category.assoc, hRt]
      _ = (hpb.lift g₁ g₂ h ≫ s.left) ≫ A.hom := by rw [Category.assoc, hRs]
      _ = g₂ ≫ A.hom := by rw [h2]
  let Mo : Over (Spec (CommRingCat.of k)) := Over.mk (EffectiveEpi.desc q A.hom hdesc)
  let qo : A ⟶ Mo := Over.homMk q (EffectiveEpi.fac q A.hom hdesc)
  refine ⟨Mo, qo, hM, hqF, hqFl, hqL, hqS, fun T a a' ↦ ?_⟩
  rw [kerOver]
  constructor
  · rintro ⟨r, rfl, rfl⟩
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Category.assoc]
    exact congrArg (r.left ≫ ·) hpb.w
  · intro h
    have h' : a.left ≫ q = a'.left ≫ q := congrArg CommaMorphism.left h
    let r0 := hpb.lift a.left a'.left h'
    have hr0 : r0 ≫ R.hom = T.hom := by
      rw [← hRs, ← Category.assoc, hpb.lift_snd]
      exact Over.w a'
    refine ⟨Over.homMk r0 hr0, ?_, ?_⟩
    · exact Over.OverMorphism.ext (hpb.lift_fst _ _ h')
    · exact Over.OverMorphism.ext (hpb.lift_snd _ _ h')

end Core

/-- The value of a natural transformation out of a represented functor at a test morphism. -/
lemma app_up_eq {C : Type*} [Category.{u} C] {X : C} {P : Cᵒᵖ ⥤ Type (max u w)}
    (f : uliftYoneda.{w}.obj X ⟶ P) {T : C} (a : T ⟶ X) :
    f.app (op T) ⟨a⟩ = P.map a.op (uliftYonedaEquiv f) := by
  have h := NatTrans.naturality_apply f a.op (⟨𝟙 X⟩ : (uliftYoneda.{w}.obj X).obj (op X))
  rw [uliftYonedaEquiv_apply, ← h]
  congr 1
  apply ULift.ext
  exact (Category.comp_id a).symm

variable (k) in
/-- Descent of an invariant affine open of `F × Spec L` along a finite field extension `L/k`. -/
theorem isLFTAffineOpen_universalImage_fst
    (h03BM : FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u})
    {F : Presheaf (Spec (CommRingCat.of k))}
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology _) F)
    (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
    {W : Subfunctor (extProd F (specOver k L))} (hW : IsLFTAffineOpen W)
    (hinv : ∀ (T : (Over (Spec (CommRingCat.of k)))ᵒᵖ) (x y : (extProd F (specOver k L)).obj T),
      extProd.fst.app T x = extProd.fst.app T y → (x ∈ W.obj T ↔ y ∈ W.obj T)) :
    IsLFTAffineOpen (universalImage extProd.fst W) ∧
      (universalImage extProd.fst W).preimage extProd.fst = W := by
  let Λ := specOver k L
  let W₀ := universalImage (extProd.fst : extProd F Λ ⟶ F) W
  have hpre : W₀.preimage extProd.fst = W :=
    OpenSubfunctorDescent.universalImage_preimage_eq_of_invariant extProd.fst W hinv
  have hfin : IsFinite (extProd.fst : extProd F Λ ⟶ F) :=
    extProd.relative_fst (@_root_.AlgebraicGeometry.IsFinite) inferInstance
  have hopen : IsOpenImmersion W₀.ι :=
    OpenSubfunctorDescent.universalImage_open_of_finite _ hfin W hW.1
  refine ⟨⟨hopen, ?_⟩, hpre⟩
  obtain ⟨A, hA, hAlft, ⟨e⟩⟩ := hW.2
  let j : (schemeYoneda _).obj A ⟶ extProd F Λ := e.hom ≫ W.ι
  have hj : ∀ {T : Over (Spec (CommRingCat.of k))} (a : T ⟶ A),
      j.app (op T) ⟨a⟩ = (F.map a.op (uliftYonedaEquiv j).1,
        ULift.up (a ≫ (uliftYonedaEquiv j).2.down)) := by
    intro T a
    rw [app_up_eq]
    rfl
  let x₀ := (uliftYonedaEquiv j).1
  let α₀ : A ⟶ Λ := (uliftYonedaEquiv j).2.down
  have hhominv : ∀ T (w : ((schemeYoneda _).obj A).obj T), e.inv.app T (e.hom.app T w) = w :=
    fun T w ↦ ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id T) w
  have hinvhom : ∀ T (w : W.toFunctor.obj T), e.hom.app T (e.inv.app T w) = w :=
    fun T w ↦ ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id T) w
  have hjinj : ∀ T, Function.Injective (j.app T) := by
    intro T x y hxy
    have h1 : e.hom.app T x = e.hom.app T y := Subtype.ext hxy
    rw [← hhominv T x, ← hhominv T y, h1]
  have hjW : ∀ {T : Over (Spec (CommRingCat.of k))} (a : T ⟶ A), j.app (op T) ⟨a⟩ ∈ W.obj (op T) :=
    fun a ↦ (e.hom.app _ ⟨a⟩).2
  have hjsurj : ∀ {T : Over (Spec (CommRingCat.of k))} (z : (extProd F Λ).obj (op T)),
      z ∈ W.obj (op T) → ∃ a : T ⟶ A, j.app (op T) ⟨a⟩ = z := by
    intro T z hz
    refine ⟨(e.inv.app (op T) ⟨z, hz⟩).down, ?_⟩
    change (e.hom.app _ (e.inv.app (op T) ⟨z, hz⟩)).1 = z
    rw [hinvhom]
  have inj : ∀ (T : Over (Spec (CommRingCat.of k))) (a a' : T ⟶ A),
      F.map a.op x₀ = F.map a'.op x₀ → a ≫ α₀ = a' ≫ α₀ → a = a' := by
    intro T a a' h1 h2
    have := hjinj (op T) (a₁ := ⟨a⟩) (a₂ := ⟨a'⟩) (by rw [hj, hj, h1, h2])
    exact congrArg ULift.down this
  have lift : ∀ (T : Over (Spec (CommRingCat.of k))) (a : T ⟶ A) (β : T ⟶ Λ),
      ∃ a' : T ⟶ A, F.map a'.op x₀ = F.map a.op x₀ ∧ a' ≫ α₀ = β := by
    intro T a β
    have hmem : ((F.map a.op x₀, ULift.up β) : (extProd F Λ).obj (op T)) ∈ W.obj (op T) := by
      apply (hinv (op T) (j.app (op T) ⟨a⟩) _ ?_).mp (hjW a)
      rw [hj]
      rfl
    obtain ⟨a', ha'⟩ := hjsurj _ hmem
    rw [hj] at ha'
    exact ⟨a', congrArg Prod.fst ha', congrArg ULift.down (congrArg Prod.snd ha')⟩
  obtain ⟨M, q, hM, hqF, hqFl, hqL, hqS, hker⟩ :=
    exists_affine_quotient h03BM x₀ α₀ inj lift
  -- the presentation of `W₀` by `A`
  have hle : Subfunctor.range (j ≫ extProd.fst) ≤ W₀ := by
    rintro T _ ⟨⟨a⟩, rfl⟩
    have h1 : j.app T ⟨a⟩ ∈ (W₀.preimage extProd.fst).obj T := by rw [hpre]; exact hjW a
    exact h1
  let aW : (schemeYoneda _).obj A ⟶ W₀.toFunctor := Subfunctor.lift (j ≫ extProd.fst) hle
  have haW : ∀ {T : Over (Spec (CommRingCat.of k))} (a : T ⟶ A),
      (aW.app (op T) ⟨a⟩).1 = F.map a.op x₀ := by
    intro T a
    change extProd.fst.app _ (j.app (op T) ⟨a⟩) = _
    rw [hj]
    rfl
  have hsh : CategoryTheory.Presheaf.IsSheaf (fppfTopology _) W₀.toFunctor :=
    OpenSubfunctorImages.isSheaf_of_open hF hopen
  let W₀s : FppfSheaf (Spec (CommRingCat.of k)) := ⟨W₀.toFunctor, hsh⟩
  have hls : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology _) aW := by
    constructor
    intro T y
    have : Flat (prod.fst : T ⨯ Λ ⟶ T).left := extProd.prod_fst_left (@Flat) inferInstance
    have : LocallyOfFinitePresentation (prod.fst : T ⨯ Λ ⟶ T).left :=
      extProd.prod_fst_left (@LocallyOfFinitePresentation) inferInstance
    have : Surjective (prod.fst : T ⨯ Λ ⟶ T).left :=
      extProd.prod_fst_left (@Surjective) inferInstance
    apply (fppfTopology _).superset_covering ?_
      (generate_singleton_mem_fppfTopology (prod.fst : T ⨯ Λ ⟶ T))
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    let z : (extProd F Λ).obj (op (T ⨯ Λ)) := (F.map (prod.fst : T ⨯ Λ ⟶ T).op y.1,
      ULift.up prod.snd)
    have hz : z ∈ W.obj _ := by
      rw [← hpre]
      exact W₀.map _ y.2
    obtain ⟨a, ha⟩ := hjsurj z hz
    refine ⟨⟨a⟩, ?_⟩
    apply Subtype.ext
    rw [haW]
    have := congrArg Prod.fst ha
    rw [hj] at this
    exact this
  have hkerW : ∀ (T : Over (Spec (CommRingCat.of k))) (w₁ w₂ : T ⟶ A),
      aW.app (op T) ⟨w₁⟩ = aW.app (op T) ⟨w₂⟩ ↔ w₁ ≫ q = w₂ ≫ q := by
    intro T w₁ w₂
    rw [← hker, Subtype.ext_iff, haW, haW]
  obtain ⟨e', -⟩ := exists_iso_of_locallySurjective_of_same_kernel (F := W₀s) aW q hls
    (isLocallySurjective_schemeYoneda_map q) hkerW
  have hMlft : LocallyOfFiniteType M.hom := by
    have : LocallyOfFiniteType (q.left ≫ M.hom) := by rw [Over.w q]; exact hAlft
    exact FiniteFlatSourceDescent.locallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
      q.left M.hom
  exact ⟨M, hM, hMlft, ⟨e'⟩⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
