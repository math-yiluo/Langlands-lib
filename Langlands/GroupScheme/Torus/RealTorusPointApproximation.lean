import Langlands.Global.RealCompletionEmbeddingSigns
import Langlands.GroupScheme.Rational.SimplyConnectedRealPlacesSurjectivity
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.RealTorusIntermediateNorm
import Langlands.GroupScheme.Torus.RealTorusNormRepresentatives
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.TorusIntermediateCocharacter

/-! # Simultaneous approximation of real torus points modulo norms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 170000

namespace Langlands.GroupScheme.RealTorusNorm

private theorem extend_norm_of_card_two (K M : Type u) [Field K] [Field M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (S : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine S.X.left]
    (hcard : Nat.card (M ≃ₐ[K] M) = 2) (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1)
    (r : Lie.AffinePoints S.toGrp M) :
    GaloisPoint.extend K M S.toGrp (GaloisPoint.norm K M S r) =
      r * GaloisPoint.conjugate K M S.toGrp σ r := by
  classical
  obtain ⟨τ, _, hτ⟩ := (Nat.card_eq_two_iff' (1 : M ≃ₐ[K] M)).mp hcard
  have hall : (Finset.univ : Finset (M ≃ₐ[K] M)) = {1, σ} := by
    refine Finset.ext fun g => ?_
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hg : g = 1
    · exact Or.inl hg
    · exact Or.inr ((hτ g hg).trans (hτ σ hσ).symm)
  rw [GaloisPoint.extend_norm, hall, Finset.prod_insert (Finset.notMem_singleton.mpr hσ.symm),
    Finset.prod_singleton, GaloisPoint.conjugate_one]

private theorem congr_fixed_of_congr_fixed {S : Scheme.{u}} {A B : CommGroupScheme S}
    (i : A ≅ B) (f : cocharacterLattice A → cocharacterLattice A)
    (g : cocharacterLattice B → cocharacterLattice B)
    (h : ∀ x, cocharacterLattice.congr i (f x) = g (cocharacterLattice.congr i x))
    (y : cocharacterLattice B) (hy : g y = y) :
    f (cocharacterLattice.congr i.symm y) = cocharacterLattice.congr i.symm y := by
  have hi : cocharacterLattice.congr i (cocharacterLattice.congr i.symm y) = y := by
    change (y ≫ i.inv) ≫ i.hom = y
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cocharacterLattice.congr i).injective
  rw [h, hi, hy]

section DirectCocharacters

variable (k K M : Type u) [Field k] [Field K] [Field M]
  [Algebra k K] [Algebra k M] [Algebra K M] [IsScalarTower k K M]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

local notation "TK" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T
local notation "TM" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k M)) T
local notation "TKM" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap K M)) TK
local notation "e" => StarActionFiniteStage.towerIsoOf (algebraBaseMap k K)
  (algebraBaseMap K M) T (algebraBaseMap k M) Lie.algebraBaseMap_tower

private theorem directCocharacter_fixed (hTM : IsSplitTorus (TM).toGrp) (σ : M ≃ₐ[K] M)
    (ν : cocharacterLattice TKM)
    (hν : cocharacterLattice.galoisRepresentation K M TK σ ν = ν) :
    cocharacterLattice.galoisRepresentation k M T (σ.restrictScalars k)
        (cocharacterLattice.congr (e).symm ν) = cocharacterLattice.congr (e).symm ν :=
  congr_fixed_of_congr_fixed e _ _
    (cocharacterLattice.galoisRepresentation_scalarExtension k K M T hTM σ) ν hν

local notation "πT" σ:max => quadraticClass k K M T σ
local notation "βT" => Lie.affineBaseChangeEquiv k K T.toGrp M
local notation "VK" ν:max => WeilGm.cocharacterValue K M TK (CommGroupScheme.groupHom ν) M
local notation "VM" eta:max => WeilGm.cocharacterValue k M T (CommGroupScheme.groupHom eta) M

private theorem localClass_eq_cocharacterValue (σ : M ≃ₐ[K] M)
    (p : Lie.AffinePoints (TK).toGrp K) (ν : cocharacterLattice TKM) (a : Mˣ)
    (r : Lie.AffinePoints (TK).toGrp M)
    (h : GaloisPoint.extend K M (TK).toGrp p =
      (VK ν) a * (r * GaloisPoint.conjugate K M (TK).toGrp σ r)) :
    (πT σ) (βT (GaloisPoint.extend K M (TK).toGrp p)) = (πT σ) (βT ((VK ν) a)) := by
  have hr : βT (GaloisPoint.conjugate K M (TK).toGrp σ r) =
      GaloisPoint.conjugate k M T.toGrp (σ.restrictScalars k) (βT r) :=
    Lie.affineBaseChangeEquiv_naturality k K T.toGrp σ.toAlgHom r
  rw [h, map_mul βT, map_mul βT, hr, map_mul (πT σ), quadraticClass_product, mul_one]

private theorem exists_directRepresentative (hTM : IsSplitTorus (TM).toGrp) (σ : M ≃ₐ[K] M)
    (p : Lie.AffinePoints (TK).toGrp K) (ν : cocharacterLattice TKM) (a : Mˣ)
    (r : Lie.AffinePoints (TK).toGrp M)
    (hν : cocharacterLattice.galoisRepresentation K M TK σ ν = ν)
    (h : GaloisPoint.extend K M (TK).toGrp p =
      (VK ν) a * (r * GaloisPoint.conjugate K M (TK).toGrp σ r)) :
    ∃ eta : cocharacterLattice TM,
      cocharacterLattice.galoisRepresentation k M T (σ.restrictScalars k) eta = eta ∧
      (πT σ) (βT (GaloisPoint.extend K M (TK).toGrp p)) = (πT σ) ((VM eta) a) :=
  ⟨cocharacterLattice.congr (e).symm ν,
    directCocharacter_fixed k K M T hTM σ ν hν,
    (localClass_eq_cocharacterValue k K M T σ p ν a r h).trans
      (congrArg (fun x : Lie.AffinePoints T.toGrp M => (πT σ) x)
        (cocharacterLattice.cocharacterValue_towerIso k K M T ν a).symm)⟩

private theorem exists_norm_of_class_eq [FiniteDimensional K M] [IsGalois K M]
    [IsAffine (TK).X.left] (hcard : Nat.card (M ≃ₐ[K] M) = 2)
    (σ : M ≃ₐ[K] M) (hσ : σ ≠ 1)
    (z : Lie.AffinePoints T.toGrp k) (p : Lie.AffinePoints (TK).toGrp K)
    (h : (πT σ) (βT (GaloisPoint.extend K M (TK).toGrp p)) =
      (πT σ) (GaloisPoint.extend k M T.toGrp z)) :
    ∃ q : Lie.AffinePoints (TK).toGrp M,
      p = (show Lie.AffinePoints (TK).toGrp K from
        (Lie.affineBaseChangeEquiv k K T.toGrp K).symm (GaloisPoint.extend k K T.toGrp z)) *
        (show Lie.AffinePoints (TK).toGrp K from GaloisPoint.norm K M (TK) q) := by
  obtain ⟨r, hr⟩ := (quadraticClass_eq_iff k K M T σ _ _).mp h
  let βK := Lie.affineBaseChangeEquiv k K T.toGrp K
  let q := (βT).symm r
  have hq : βT q = r := (βT).apply_symm_apply r
  have hglobal :
      βT (GaloisPoint.extend K M (TK).toGrp (βK.symm (GaloisPoint.extend k K T.toGrp z))) =
        GaloisPoint.extend k M T.toGrp z := by
    rw [show βT (GaloisPoint.extend K M (TK).toGrp
      (βK.symm (GaloisPoint.extend k K T.toGrp z))) =
      Lie.affineMap T.toGrp ((Algebra.ofId K M).restrictScalars k)
        (βK (βK.symm (GaloisPoint.extend k K T.toGrp z))) from
      Lie.affineBaseChangeEquiv_naturality k K T.toGrp (Algebra.ofId K M) _,
      MulEquiv.apply_symm_apply]
    change Lie.affineMap T.toGrp ((Algebra.ofId K M).restrictScalars k)
      (Lie.affineMap T.toGrp (Algebra.ofId k K) z) = _
    rw [← Lie.affineMap_comp]
    exact congrArg (fun f : k →ₐ[k] M => Lie.affineMap T.toGrp f z)
      (AlgHom.ext fun a => (IsScalarTower.algebraMap_apply k K M a).symm)
  have hconj : βT (GaloisPoint.conjugate K M (TK).toGrp σ q) =
      GaloisPoint.conjugate k M T.toGrp (σ.restrictScalars k) (βT q) :=
    Lie.affineBaseChangeEquiv_naturality k K T.toGrp σ.toAlgHom q
  refine ⟨q, GaloisPoint.extend_injective K M (TK).toGrp ((βT).injective ?_)⟩
  rw [map_mul (GaloisPoint.extend K M (TK).toGrp), map_mul βT, hglobal,
    extend_norm_of_card_two K M (TK) hcard σ hσ, map_mul βT, hconj, hq, hr]

end DirectCocharacters

variable {F : Type u} [Field F]

local notation "K[" w "]" => InfinitePlace.Completion (Subtype.val w)
local notation "M[" w "]" => AlgebraicClosure (K[w])
local notation "realIso[" w "]" => InfinitePlace.Completion.ringEquivRealOfIsReal (Subtype.property w)

private theorem closure_finrank (w : RealPlaceIndex F) : Module.finrank (K[w]) (M[w]) = 2 :=
  Langlands.FieldTheory.finrank_algebraicClosure_of_equiv_real (realIso[w])

/-- The algebraic closure of the completion at a real place is finite over it. -/
theorem completionClosure_finiteDimensional (w : RealPlaceIndex F) :
    FiniteDimensional (K[w]) (M[w]) :=
  FiniteDimensional.of_finrank_pos (by rw [closure_finrank w]; decide)

attribute [local instance] completionClosure_finiteDimensional

private instance completionCharZero (w : RealPlaceIndex F) : CharZero (K[w]) :=
  charZero_of_injective_ringHom (f := (realIso[w]).symm.toRingHom) (realIso[w]).symm.injective

private theorem card_completionAut (w : RealPlaceIndex F) :
    Nat.card (M[w] ≃ₐ[K[w]] M[w]) = 2 :=
  (IsGalois.card_aut_eq_finrank _ _).trans (closure_finrank w)

private theorem exists_completionConjugation (w : RealPlaceIndex F) :
    ∃ σ : M[w] ≃ₐ[K[w]] M[w], σ ≠ 1 := by
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : M[w] ≃ₐ[K[w]] M[w])).mp
    (card_completionAut w)
  exact ⟨σ, hσ⟩

private def completionConjugation (w : RealPlaceIndex F) :
    M[w] ≃ₐ[K[w]] M[w] :=
  (exists_completionConjugation w).choose

private theorem completionConjugation_ne_one (w : RealPlaceIndex F) :
    completionConjugation w ≠ 1 :=
  (exists_completionConjugation w).choose_spec

private theorem completionConjugation_mul_self (w : RealPlaceIndex F) :
    completionConjugation w * completionConjugation w = 1 := by
  simpa only [card_completionAut w, pow_two] using pow_card_eq_one' (x := completionConjugation w)

variable (T : CommGroupScheme (Spec (CommRingCat.of F)))

local notation "T[" w "]" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap F (K[w]))) T
local notation "TM[" w "]" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap F (M[w]))) T
local notation "σ[" w "]" => completionConjugation w
local notation "π[" w "]" => quadraticClass F (K[w]) (M[w]) T (σ[w])
local notation "β[" w "," A "]" => Lie.affineBaseChangeEquiv F (K[w]) T.toGrp A
local notation "j[" w "]" => IsScalarTower.toAlgHom F (K[w]) (M[w])
local notation "globalClass[" w "]" => MonoidHom.comp (π[w]) (GaloisPoint.extend F (M[w]) T.toGrp)
local notation "localClass[" w "]" =>
  MonoidHom.comp (π[w]) (MonoidHom.comp (MulEquiv.toMonoidHom (β[w, M[w]]))
    (GaloisPoint.extend (K[w]) (M[w]) (CommGroupScheme.toGrp (T[w]))))

private theorem exists_localCocharacter (hT : IsTorus T.toGrp) (w : RealPlaceIndex F)
    (p : Lie.AffinePoints (T[w]).toGrp (K[w])) :
    ∃ eta : cocharacterLattice (TM[w]),
      cocharacterLattice.galoisRepresentation F (M[w]) T ((σ[w]).restrictScalars F) eta = eta ∧
      π[w] (β[w, M[w]] (GaloisPoint.extend (K[w]) (M[w]) (T[w]).toGrp p)) =
        π[w] (WeilGm.cocharacterValue F (M[w]) T (CommGroupScheme.groupHom eta) (M[w]) (-1)) := by
  obtain ⟨ν, r, hν, hp⟩ :=
    realTorusNormRepresentatives (K[w]) (realIso[w]) (T[w]) (hT.baseChange (K := K[w])) p
  have hTM : IsSplitTorus (TM[w]).toGrp :=
    (hT.baseChange (K := M[w])).isRelativeTorus.isSplitTorus_of_isAlgClosed
  exact exists_directRepresentative F (K[w]) (M[w]) T hTM (σ[w]) p ν (-1) r
    (hν (σ[w])) (hp (σ[w]) (completionConjugation_ne_one w))

variable {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

private theorem exists_intermediateRepresentative (hT : IsTorus T.toGrp)
    (hTE : IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F E)).obj T.toGrp))
    (w : RealPlaceIndex F) (e : E →ₐ[F] M[w]) (p : Lie.AffinePoints (T[w]).toGrp (K[w])) :
    ∃ (N : IntermediateField F E)
      (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F N)).obj T))
      (f : N →ₐ[F] K[w]),
      (IsScalarTower.toAlgHom F (K[w]) (M[w])).comp f = e.comp N.val ∧
      π[w] (β[w, M[w]] (GaloisPoint.extend (K[w]) (M[w]) (T[w]).toGrp p)) =
        π[w] (Lie.affineMap T.toGrp (e.comp N.val)
          (WeilGm.cocharacterValue F N T (CommGroupScheme.groupHom ν) N (-1))) := by
  let : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  let : IsAffineHom T.X.hom := inferInstance
  let : Algebra E (M[w]) := e.toRingHom.toAlgebra
  let : IsScalarTower F E (M[w]) := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  obtain ⟨eta, heta, hp⟩ := exists_localCocharacter T hT w p
  obtain ⟨N, ν, hfix, hval⟩ :=
    exists_intermediateCocharacter F E (M[w]) T hTE ((σ[w]).restrictScalars F) eta heta
  have hfix' (x : N) : (σ[w]) ((e.comp N.val) x) = (e.comp N.val) x := hfix x
  obtain ⟨f, hf⟩ := exists_baseEmbedding F (K[w]) (M[w])
    (card_completionAut w) (σ[w]) (completionConjugation_ne_one w) (e.comp N.val) hfix'
  exact ⟨N, ν, f, hf, hp.trans (congrArg (π[w]) hval)⟩

omit [FiniteDimensional F E] [IsGalois F E] in
private theorem fixedEmbedding_factors (w : RealPlaceIndex F) (N : IntermediateField F E)
    (e : E →ₐ[F] M[w]) {i : N →ₐ[F] E} (hi : ∀ x : N, σ[w] (e (i x)) = e (i x)) :
    ∃ f : N →ₐ[F] K[w], (j[w]).comp f = e.comp i :=
  exists_baseEmbedding F (K[w]) (M[w]) (card_completionAut w) (σ[w])
    (completionConjugation_ne_one w) (e.comp i) hi

open scoped Classical in
private theorem class_intermediateNorm [IsAffine T.X.left] (w : RealPlaceIndex F)
    (N : IntermediateField F E) (e : E →ₐ[F] M[w]) (x : Lie.AffinePoints T.toGrp N) :
    (globalClass[w]) (GaloisPoint.intermediateNorm F E N T x) =
      ∏ i ∈ Finset.univ with (∀ a : N, σ[w] (e (i a)) = e (i a)),
        (π[w]) (Lie.affineMap T.toGrp (e.comp i) x) := by
  let : Algebra E (M[w]) := e.toRingHom.toAlgebra
  let : IsScalarTower F E (M[w]) := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  let s := conjugateEmbedding F (K[w]) (M[w]) E N (σ[w])
  have hfix (i : N →ₐ[F] E) : s i = i ↔ ∀ a : N, σ[w] (e (i a)) = e (i a) := by
    have hconj (a : N) : e (s i a) = σ[w] (e (i a)) :=
      conjugateEmbedding_apply F (K[w]) (M[w]) E N (σ[w]) i a
    constructor
    · intro hi a
      exact (hconj a).symm.trans (congrArg (fun f : N →ₐ[F] E => e (f a)) hi)
    · intro hi
      apply AlgHom.ext
      intro a
      exact e.injective ((hconj a).trans (hi a))
  change (π[w]) (GaloisPoint.extend F (M[w]) T.toGrp
    (GaloisPoint.intermediateNorm F E N T x)) = _
  rw [quadraticClass_intermediateNorm F (K[w]) (M[w]) T E N (σ[w])
    (completionConjugation_mul_self w) x]
  have hs : (Finset.univ.filter fun i => s i = i) =
      (Finset.univ.filter fun i : N →ₐ[F] E => ∀ a : N, σ[w] (e (i a)) = e (i a)) :=
    Finset.filter_congr fun i _ => hfix i
  change ∏ i ∈ Finset.univ with s i = i, (π[w]) (Lie.affineMap T.toGrp (e.comp i) x) = _
  rw [hs]

variable [NumberField F]

private theorem exists_singlePlacePoint [IsAffine T.X.left] (hT : IsTorus T.toGrp)
    (hTE : IsSplitTorus ((GroupScheme.baseChange (algebraBaseMap F E)).obj T.toGrp))
    (e : ∀ w : RealPlaceIndex F, E →ₐ[F] M[w]) (w : RealPlaceIndex F)
    (p : Lie.AffinePoints (T[w]).toGrp (K[w])) :
    ∃ z : Lie.AffinePoints T.toGrp F, globalClass[w] z = localClass[w] p ∧
      ∀ v : RealPlaceIndex F, v ≠ w → globalClass[v] z = 1 := by
  classical
  obtain ⟨N, ν, f, hf, hp⟩ := exists_intermediateRepresentative T hT hTE w (e w) p
  let : NumberField N := NumberField.of_module_finite F N
  obtain ⟨a, hneg, hpos⟩ := Langlands.Global.realCompletionEmbeddingSigns F N w f
  let V := WeilGm.cocharacterValue F N T (CommGroupScheme.groupHom ν) N
  let z := GaloisPoint.intermediateNorm F E N T (V a)
  have hproduct (v : RealPlaceIndex F) :
      globalClass[v] z = ∏ i ∈ Finset.univ with (∀ b : N, σ[v] (e v (i b)) = e v (i b)),
        π[v] (Lie.affineMap T.toGrp ((e v).comp i) (V a)) :=
    class_intermediateNorm T v N (e v) (V a)
  have hterm (v : RealPlaceIndex F) (i : N →ₐ[F] E) (g : N →ₐ[F] K[v])
      (hg : (j[v]).comp g = (e v).comp i)
      (hdiff : (⟨v, g⟩ : Σ v' : RealPlaceIndex F, N →ₐ[F] K[v']) ≠ ⟨w, f⟩) :
      π[v] (Lie.affineMap T.toGrp ((e v).comp i) (V a)) = 1 := by
    rw [← hg]
    exact quadraticClass_cocharacter_of_pos F (K[v]) (M[v]) T (σ[v]) (realIso[v]) g ν a
      (hpos v g hdiff)
  refine ⟨z, ?_, ?_⟩
  · have hfixed (b : N) : σ[w] (e w (N.val b)) = e w (N.val b) := by
      have h := DFunLike.congr_fun hf b
      change j[w] (f b) = e w (N.val b) at h
      rw [← h]
      exact (σ[w]).commutes (f b)
    rw [hproduct w, Finset.prod_eq_single_of_mem N.val
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfixed⟩)]
    · have h := quadraticClass_cocharacter_of_neg F (K[w]) (M[w]) T
        (σ[w]) (realIso[w]) f ν a hneg
      rw [hf] at h
      exact h.trans hp.symm
    · intro i hi hne
      obtain ⟨g, hg⟩ := fixedEmbedding_factors w N (e w) (Finset.mem_filter.mp hi).2
      apply hterm w i g hg
      intro h
      have hgf : g = f := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      subst g
      exact hne (AlgHom.ext fun b => (e w).injective (DFunLike.congr_fun (hg.symm.trans hf) b))
  · intro v hne
    rw [hproduct v]
    apply Finset.prod_eq_one
    intro i hi
    obtain ⟨g, hg⟩ := fixedEmbedding_factors v N (e v) (Finset.mem_filter.mp hi).2
    exact hterm v i g hg fun h => hne (congrArg Sigma.fst h)

private theorem exists_simultaneousPoint (hT : IsTorus T.toGrp)
    (p : ∀ w : RealPlaceIndex F, Lie.AffinePoints (T[w]).toGrp (K[w])) :
    ∃ z : Lie.AffinePoints T.toGrp F, ∀ w, globalClass[w] z = localClass[w] (p w) := by
  classical
  let : IsAffine T.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  let : Fintype (RealPlaceIndex F) := Fintype.ofFinite _
  obtain ⟨E, _, _, hfin, hgal, hTE⟩ := torusFiniteGaloisSplitting F T.toGrp hT
  let : FiniteDimensional F E := hfin
  let : IsGalois F E := hgal
  let e (w : RealPlaceIndex F) : E →ₐ[F] M[w] := IsAlgClosed.lift
  choose z hz using fun w => exists_singlePlacePoint T hT hTE e w (p w)
  refine ⟨∏ v, z v, fun w => ?_⟩
  rw [map_prod, Finset.prod_eq_single_of_mem w (Finset.mem_univ _) fun v _ hv => (hz v).2 w hv.symm]
  exact (hz w).1

omit [NumberField F] in
private theorem exists_completionNorm (hT : IsTorus T.toGrp) (w : RealPlaceIndex F)
    (z : Lie.AffinePoints T.toGrp F) (p : Lie.AffinePoints (T[w]).toGrp (K[w]))
    (h : localClass[w] p = globalClass[w] z) :
    letI : IsAffine (T[w]).X.left :=
      SplittingAssembly.isAffine_of_isTorus (T[w]).toGrp (hT.baseChange (K := K[w]))
    ∃ r : Lie.AffinePoints (T[w]).toGrp (M[w]),
      p = (show Lie.AffinePoints (T[w]).toGrp (K[w]) from
        (β[w, K[w]]).symm (GaloisPoint.extend F (K[w]) T.toGrp z)) *
        (show Lie.AffinePoints (T[w]).toGrp (K[w]) from
          GaloisPoint.norm (K[w]) (M[w]) (T[w]) r) := by
  let : IsAffine (T[w]).X.left :=
    SplittingAssembly.isAffine_of_isTorus (T[w]).toGrp (hT.baseChange (K := K[w]))
  exact exists_norm_of_class_eq F (K[w]) (M[w]) T (card_completionAut w) (σ[w])
    (completionConjugation_ne_one w) z p h

/-- A family of torus points over the real completions is met by a single
global point modulo the point norm from each completion's algebraic closure. -/
def RealTorusPointApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T.toGrp),
    let Tloc (w : RealPlaceIndex F) := (CommGroupScheme.baseChange (algebraBaseMap F (K[w]))).obj T
    ∀ (p : ∀ w : RealPlaceIndex F, Lie.AffinePoints (Tloc w).toGrp (K[w])),
      ∃ z : Lie.AffinePoints T.toGrp F, ∀ w : RealPlaceIndex F,
        letI : IsAffine (Tloc w).X.left :=
          SplittingAssembly.isAffine_of_isTorus (Tloc w).toGrp (hT.baseChange (K := K[w]))
        ∃ r : Lie.AffinePoints (Tloc w).toGrp (M[w]),
          p w = (show Lie.AffinePoints (Tloc w).toGrp (K[w]) from
            (Lie.affineBaseChangeEquiv F (K[w]) T.toGrp (K[w])).symm
              (GaloisPoint.extend F (K[w]) T.toGrp z)) *
            (show Lie.AffinePoints (Tloc w).toGrp (K[w]) from
              GaloisPoint.norm (K[w]) (M[w]) (Tloc w) r)

theorem realTorusPointApproximation : RealTorusPointApproximationStatement.{u} := by
  intro F _ _ T hT Tloc p
  obtain ⟨z, hz⟩ := exists_simultaneousPoint T hT p
  exact ⟨z, fun w => exists_completionNorm T hT w z (p w) (hz w).symm⟩

end Langlands.GroupScheme.RealTorusNorm
