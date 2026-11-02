import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStatements
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentUniquenessProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedProof

/-! # Proof of faithfully flat descent of isomorphisms between line bundles -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.LineBundleIsoDescent

open UnitCocycleDescentUniqueness

/-- Module morphisms agreeing after pullback to every member of an open cover agree. -/
lemma hom_ext_of_openCover {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) {A B : X.Modules}
    (f g : A ⟶ B)
    (h : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map f =
      (Scheme.Modules.pullback (𝒰.f i)).map g) :
    f = g := by
  obtain ⟨k, -, hk⟩ := OpenCoverHomGluing.openCoverHomGluing X 𝒰 A B
    (fun i ↦ (Scheme.Modules.pullback (𝒰.f i)).map f)
    (fun i j ↦ squarePullbackIso_naturality _ _ _ _ _ f)
  exact (hk f fun _ ↦ rfl).trans (hk g fun i ↦ (h i).symm).symm

section Compatible

variable {X Y : Scheme.{u}} (p : X ⟶ Y) {M N : Y.Modules}
  (e : (Scheme.Modules.pullback p).obj M ≅ (Scheme.Modules.pullback p).obj N)

/-- Compatibility of `φ : t^* M ⟶ t^* N` with `e : p^* M ≅ p^* N` at one factorization
`h ≫ t = g ≫ p`. -/
def CompatibleAt {Z T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj N)
    (g : Z ⟶ X) (h : Z ⟶ T) (hs : h ≫ t = g ≫ p) : Prop :=
  (Scheme.Modules.pullback h).map φ ≫ (squarePullbackIso p h g t hs N).hom =
    (squarePullbackIso p h g t hs M).hom ≫ (Scheme.Modules.pullback g).map e.hom

/-- Compatibility of `φ : t^* M ⟶ t^* N` with `e` at every factorization. -/
def Compatible {T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj N) : Prop :=
  ∀ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ T) (hs : h ≫ t = g ≫ p),
    CompatibleAt p e t φ g h hs

/-- Compatibility at one factorization implies compatibility at every precomposite. -/
lemma compatibleAt_precomp {Z Z' T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj N)
    (k : Z ⟶ Z') (g' : Z' ⟶ X) (h' : Z' ⟶ T) (hs' : h' ≫ t = g' ≫ p)
    (H : CompatibleAt p e t φ g' h' hs') (g : Z ⟶ X) (h : Z ⟶ T)
    (hg : k ≫ g' = g) (hh : k ≫ h' = h) (hs : h ≫ t = g ≫ p) :
    CompatibleAt p e t φ g h hs := by
  subst hg hh
  unfold CompatibleAt at H ⊢
  have n₁ := (Scheme.Modules.pullbackComp k h').hom.naturality φ
  have n₂ := (Scheme.Modules.pullbackComp k g').hom.naturality e.hom
  simp only [Functor.comp_map] at n₁ n₂
  have H' := congrArg (Scheme.Modules.pullback k).map H
  simp only [Functor.map_comp] at H'
  rw [← cancel_epi ((Scheme.Modules.pullbackComp k h').hom.app
    ((Scheme.Modules.pullback t).obj M))]
  rw [← reassoc_of% n₁, ← squarePullbackIso_precomp p t k g' h' hs' hs N, reassoc_of% H', n₂,
    squarePullbackIso_precomp_assoc p t k g' h' hs' hs M]

/-- Compatibility at the universal factorization through `X ×_Y T` implies compatibility. -/
lemma compatible_of_universal {T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj N)
    (H : CompatibleAt p e t φ (pullback.fst p t) (pullback.snd p t)
      pullback.condition.symm) :
    Compatible p e t φ := by
  intro Z g h hs
  exact compatibleAt_precomp p e t φ (pullback.lift g h hs.symm) _ _ _ H g h
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hs

/-- Compatibility is stable under change of base `u ≫ t = t'`. -/
lemma Compatible.change_base {T T' : Scheme.{u}} (t : T ⟶ Y) (u : T' ⟶ T) (t' : T' ⟶ Y)
    (hu : u ≫ t = t')
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj N)
    (H : Compatible p e t φ) :
    Compatible p e t'
      ((compIso u t t' hu M).inv ≫ (Scheme.Modules.pullback u).map φ ≫
        (compIso u t t' hu N).hom) := by
  intro Z g h' hs'
  have hs : (h' ≫ u) ≫ t = g ≫ p := by rw [Category.assoc, hu, hs']
  have H' := H Z g (h' ≫ u) hs
  unfold CompatibleAt at H' ⊢
  have n := (Scheme.Modules.pullbackComp h' u).hom.naturality φ
  simp only [Functor.comp_map] at n
  rw [← cancel_epi ((Scheme.Modules.pullback h').map (compIso u t t' hu M).hom)]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]
  rw [squarePullbackIso_change_base p t u t' hu g h' hs' hs N, reassoc_of% n, H',
    squarePullbackIso_change_base_assoc p t u t' hu g h' hs' hs M]

/-- The pullback of a global morphism whose pullback along `p` is `e` is compatible. -/
lemma compatible_pullback {T : Scheme.{u}} (t : T ⟶ Y) (E : M ⟶ N)
    (hE : (Scheme.Modules.pullback p).map E = e.hom) :
    Compatible p e t ((Scheme.Modules.pullback t).map E) := by
  intro Z g h hs
  unfold CompatibleAt
  rw [squarePullbackIso_naturality, hE]

/-- A compatible isomorphism is unique when both modules are trivial and the base change of
`p` is an epimorphism. -/
lemma compatible_unique {T : Scheme.{u}} (t : T ⟶ Y) [Epi (pullback.snd p t)]
    (τ : (Scheme.Modules.pullback t).obj M ≅ structureModule T)
    (σ : (Scheme.Modules.pullback t).obj N ≅ structureModule T)
    (φ ψ : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj N)
    (hφ : Compatible p e t φ.hom) (hψ : Compatible p e t ψ.hom) : φ = ψ := by
  apply pullbackIso_injective_of_trivializations (pullback.snd p t) τ σ
  apply Iso.ext
  have h₁ := hφ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  have h₂ := hψ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  unfold CompatibleAt at h₁ h₂
  rw [← h₂] at h₁
  simp only [Functor.mapIso_hom]
  exact (cancel_mono _).mp h₁

/-- Transporting `e` to `X ×_Y T` gives an isomorphism compatible with the canonical
comparisons for the second projection. -/
lemma squareTransport_compatible {T : Scheme.{u}} (t : T ⟶ Y)
    (he : ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
      (Scheme.Modules.pullback a).map e.hom ≫ (equalCompositeIso p a b h N).hom =
        (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e.hom)
    (U : Scheme.{u}) (a b : U ⟶ pullback p t)
    (h : a ≫ pullback.snd p t = b ≫ pullback.snd p t) :
    (Scheme.Modules.pullback a).map
        ((squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
          pullback.condition.symm M).hom ≫
          (Scheme.Modules.pullback (pullback.fst p t)).map e.hom ≫
          (squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
            pullback.condition.symm N).inv) ≫
        (equalCompositeIso (pullback.snd p t) a b h
          ((Scheme.Modules.pullback t).obj N)).hom =
      (equalCompositeIso (pullback.snd p t) a b h ((Scheme.Modules.pullback t).obj M)).hom ≫
        (Scheme.Modules.pullback b).map
          ((squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
            pullback.condition.symm M).hom ≫
            (Scheme.Modules.pullback (pullback.fst p t)).map e.hom ≫
            (squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
              pullback.condition.symm N).inv) := by
  have h' : (a ≫ pullback.fst p t) ≫ p = (b ≫ pullback.fst p t) ≫ p := by
    simp only [Category.assoc, pullback.condition, reassoc_of% h]
  have sM := equalCompositeIso_square p (pullback.snd p t) (pullback.fst p t) t
    pullback.condition.symm M a b h h'
  have sN := equalCompositeIso_square p (pullback.snd p t) (pullback.fst p t) t
    pullback.condition.symm N a b h h'
  have ha := (Scheme.Modules.pullbackComp a (pullback.fst p t)).hom.naturality e.hom
  have hb := (Scheme.Modules.pullbackComp b (pullback.fst p t)).hom.naturality e.hom
  simp only [Functor.comp_map] at ha hb
  have hE := he U (a ≫ pullback.fst p t) (b ≫ pullback.fst p t) h'
  rw [← cancel_mono ((Scheme.Modules.pullback b).map
    (squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
      pullback.condition.symm N).hom ≫
      (Scheme.Modules.pullbackComp b (pullback.fst p t)).hom.app
        ((Scheme.Modules.pullback p).obj N))]
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [← sN]
  simp only [Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% ha, hE, reassoc_of% sM, hb]

/-- Existence of a compatible isomorphism over a base on which both modules are trivial. -/
lemma exists_compatible {T : Scheme.{u}} (t : T ⟶ Y) [QuasiCompact p] [Flat p]
    [Surjective p]
    (he : ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
      (Scheme.Modules.pullback a).map e.hom ≫ (equalCompositeIso p a b h N).hom =
        (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map e.hom)
    (τ : (Scheme.Modules.pullback t).obj M ≅ structureModule T)
    (σ : (Scheme.Modules.pullback t).obj N ≅ structureModule T) :
    ∃ φ : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj N,
      Compatible p e t φ.hom := by
  obtain ⟨φ, hφ, -⟩ := compatibleIsoDescent_of_trivializations (pullback.snd p t) τ σ
    (squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t pullback.condition.symm M ≪≫
      (Scheme.Modules.pullback (pullback.fst p t)).mapIso e ≪≫
      (squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
        pullback.condition.symm N).symm)
    (fun U a b h ↦ squareTransport_compatible p e t he U a b h)
  refine ⟨φ, compatible_of_universal p e t φ.hom ?_⟩
  unfold CompatibleAt
  have hφ' := congrArg Iso.hom hφ
  simp only [Functor.mapIso_hom] at hφ'
  rw [hφ']
  simp

end Compatible

/-- Faithfully flat descent of isomorphisms between line bundles. -/
theorem lineBundleIsoDescent : LineBundleIsoDescentStatement.{u} := by
  intro X Y p hpqc hpflat hpsurj M N hM hN e he
  have := hpqc
  have := hpflat
  have := hpsurj
  let L : LineBundle Y := ⟨M, hM⟩
  let L' : LineBundle Y := ⟨N, hN⟩
  let V : Y → Y.Opens := fun y ↦ L.trivializingOpen y ⊓ L'.trivializingOpen y
  have hV : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun y _ ↦ ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨y, ⟨L.mem_trivializingOpen y, L'.mem_trivializingOpen y⟩⟩
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hL : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj M ≅
      structureModule (𝒰.X i)) :=
    fun i ↦ nonempty_trivial_of_le L i (V i) inf_le_left
  have hL' : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj N ≅
      structureModule (𝒰.X i)) :=
    fun i ↦ nonempty_trivial_of_le L' i (V i) inf_le_right
  -- Uniqueness: two descents of `e` agree after pullback to every cover member.
  have huniq : ∀ e₁ e₂ : M ≅ N, (Scheme.Modules.pullback p).mapIso e₁ = e →
      (Scheme.Modules.pullback p).mapIso e₂ = e → e₁ = e₂ := by
    intro e₁ e₂ h₁ h₂
    apply Iso.ext
    apply hom_ext_of_openCover 𝒰
    intro i
    have c₁ := compatible_pullback p e (𝒰.f i) e₁.hom (by rw [← h₁]; rfl)
    have c₂ := compatible_pullback p e (𝒰.f i) e₂.hom (by rw [← h₂]; rfl)
    have := compatible_unique p e (𝒰.f i) (hL i).some (hL' i).some
      ((Scheme.Modules.pullback (𝒰.f i)).mapIso e₁)
      ((Scheme.Modules.pullback (𝒰.f i)).mapIso e₂) c₁ c₂
    exact congrArg Iso.hom this
  have hE : ∀ i, ∃ φ : (Scheme.Modules.pullback (𝒰.f i)).obj M ≅
      (Scheme.Modules.pullback (𝒰.f i)).obj N, Compatible p e (𝒰.f i) φ.hom :=
    fun i ↦ exists_compatible p e (𝒰.f i) he (hL i).some (hL' i).some
  choose E hEc using hE
  obtain ⟨E₀, hE₀, -⟩ := openCoverIsoGluing_of_homGluing OpenCoverHomGluing.openCoverHomGluing
    Y 𝒰 M N E (by
    intro i j
    let w := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
    have hw : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j = w := pullback.condition.symm
    have h₁ := Compatible.change_base p e (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j)) w rfl
      _ (hEc i)
    have h₂ := Compatible.change_base p e (𝒰.f j) (pullback.snd (𝒰.f i) (𝒰.f j)) w hw
      _ (hEc j)
    have heq := compatible_unique p e w
      (nonempty_trivial_change_base (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j)) w rfl
        (hL i)).some
      (nonempty_trivial_change_base (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j)) w rfl
        (hL' i)).some
      ((compIso _ _ w rfl M).symm ≪≫
        (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).mapIso (E i) ≪≫
          compIso _ _ w rfl N)
      ((compIso _ _ w hw M).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).mapIso (E j) ≪≫
          compIso _ _ w hw N)
      (by simpa using h₁) (by simpa using h₂)
    have heq' := congrArg Iso.hom heq
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at heq'
    rw [squarePullbackIso_hom_eq_compIso _ _ _ _ _ w rfl hw,
      squarePullbackIso_hom_eq_compIso _ _ _ _ _ w rfl hw]
    rw [← cancel_epi (compIso _ _ w rfl M).inv,
      ← cancel_mono (compIso _ _ w hw N).hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
      using heq')
  refine ⟨E₀, ?_, fun e₁ h₁ ↦ huniq e₁ E₀ h₁ ?_⟩ <;>
  · -- Existence: `p^* E₀ = e`, checked on the pulled-back cover of `X`.
    apply Iso.ext
    apply hom_ext_of_openCover (𝒰.pullback₁ p)
    intro i
    have hs : pullback.snd p (𝒰.f i) ≫ 𝒰.f i = pullback.fst p (𝒰.f i) ≫ p :=
      pullback.condition.symm
    have c := hEc i _ (pullback.fst p (𝒰.f i)) (pullback.snd p (𝒰.f i)) hs
    unfold CompatibleAt at c
    have n := squarePullbackIso_naturality p (pullback.snd p (𝒰.f i))
      (pullback.fst p (𝒰.f i)) (𝒰.f i) hs E₀.hom
    rw [hE₀ i, c] at n
    exact ((cancel_epi _).mp n).symm

end Langlands.Scheme.Modules.LineBundleIsoDescent
