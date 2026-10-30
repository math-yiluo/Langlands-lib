import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentStatements
import Langlands.AlgebraicGeometry.Modules.TrivialIsoDescentProof
import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Langlands.AlgebraicGeometry.Modules.OpenCoverIsoGluing
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing

/-! # Proof of descent uniqueness for line bundles with trivialized pullback -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule
open Langlands.SchemeModule.RigidifiedModule

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

namespace Langlands.Scheme.Modules.UnitCocycleDescentUniqueness

section Compatible

variable {X Y : Scheme.{u}} (p : X ⟶ Y) {M M' : Y.Modules}
  (α : (Scheme.Modules.pullback p).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
  (α' : (Scheme.Modules.pullback p).obj M' ≅ SheafOfModules.unit X.ringCatSheaf)

/-- The comparison `u^* t^* N ≅ t'^* N` attached to an equation `u ≫ t = t'`. -/
def compIso {T T' : Scheme.{u}} (u : T' ⟶ T) (t : T ⟶ Y) (t' : T' ⟶ Y) (e : u ≫ t = t')
    (N : Y.Modules) :
    (Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback t).obj N) ≅
      (Scheme.Modules.pullback t').obj N :=
  (Scheme.Modules.pullbackComp u t).app N ≪≫ (Scheme.Modules.pullbackCongr e).app N

lemma compIso_hom {T T' : Scheme.{u}} (u : T' ⟶ T) (t : T ⟶ Y) (t' : T' ⟶ Y)
    (e : u ≫ t = t') (N : Y.Modules) :
    (compIso u t t' e N).hom = compHom u t t' e N :=
  rfl

/-- The square comparison is the forward composite comparison followed by the inverse one. -/
lemma squarePullbackIso_hom_eq_compIso {X' Y' W : Scheme.{u}} (r : Y' ⟶ Y) (p' : W ⟶ X')
    (s : W ⟶ Y') (t : X' ⟶ Y) (hs : p' ≫ t = s ≫ r) (w : W ⟶ Y)
    (e₁ : p' ≫ t = w) (e₂ : s ≫ r = w) (N : Y.Modules) :
    (squarePullbackIso r p' s t hs N).hom =
      (compIso p' t w e₁ N).hom ≫ (compIso s r w e₂ N).inv := by
  subst e₁
  simp [squarePullbackIso, compIso, Scheme.Modules.pullbackCongr]

/-- The square comparison expressed through `compHom`. -/
lemma squarePullbackIso_hom_eq_compHom {Z T : Scheme.{u}} (t : T ⟶ Y) (g : Z ⟶ X)
    (h : Z ⟶ T) (hs : h ≫ t = g ≫ p) (N : Y.Modules) :
    (squarePullbackIso p h g t hs N).hom =
      compHom h t (g ≫ p) hs N ≫ (Scheme.Modules.pullbackComp g p).inv.app N := by
  simp [squarePullbackIso, compHom]

/-- Square comparisons are compatible with precomposition by `k : Z ⟶ Z'`. -/
@[reassoc]
lemma squarePullbackIso_precomp {Z Z' T : Scheme.{u}} (t : T ⟶ Y) (k : Z ⟶ Z')
    (g' : Z' ⟶ X) (h' : Z' ⟶ T) (hs' : h' ≫ t = g' ≫ p)
    (hs : (k ≫ h') ≫ t = (k ≫ g') ≫ p) (N : Y.Modules) :
    (Scheme.Modules.pullback k).map (squarePullbackIso p h' g' t hs' N).hom ≫
        (Scheme.Modules.pullbackComp k g').hom.app ((Scheme.Modules.pullback p).obj N) =
      (Scheme.Modules.pullbackComp k h').hom.app ((Scheme.Modules.pullback t).obj N) ≫
        (squarePullbackIso p (k ≫ h') (k ≫ g') t hs N).hom := by
  have e := squarePullbackIso_comp p h' g' t hs' N k ((k ≫ g') ≫ p) rfl hs
  rw [compHom_rfl] at e
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (k ≫ g') p).hom.app N)]
  simp only [Category.assoc]
  rw [e, squarePullbackIso_hom_eq_compHom]
  simp

/-- Square comparisons are compatible with a change of the base map `u ≫ t = t'`. -/
@[reassoc]
lemma squarePullbackIso_change_base {Z T T' : Scheme.{u}} (t : T ⟶ Y) (u : T' ⟶ T)
    (t' : T' ⟶ Y) (e : u ≫ t = t') (g : Z ⟶ X) (h' : Z ⟶ T') (hs' : h' ≫ t' = g ≫ p)
    (hs : (h' ≫ u) ≫ t = g ≫ p) (N : Y.Modules) :
    (Scheme.Modules.pullback h').map (compIso u t t' e N).hom ≫
        (squarePullbackIso p h' g t' hs' N).hom =
      (Scheme.Modules.pullbackComp h' u).hom.app ((Scheme.Modules.pullback t).obj N) ≫
        (squarePullbackIso p (h' ≫ u) g t hs N).hom := by
  have e₁ := compHom_assoc h' u t (h' ≫ u) t' (g ≫ p) rfl e hs hs' N
  rw [compHom_rfl] at e₁
  rw [squarePullbackIso_hom_eq_compHom, squarePullbackIso_hom_eq_compHom, compIso_hom,
    reassoc_of% e₁]

/-- Compatibility of `φ : t^* M ⟶ t^* M'` with the trivializations `α` and `α'` at one
factorization `h ≫ t = g ≫ p`. -/
def CompatibleAt {Z T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj M')
    (g : Z ⟶ X) (h : Z ⟶ T) (hs : h ≫ t = g ≫ p) : Prop :=
  (Scheme.Modules.pullback h).map φ ≫ (squarePullbackIso p h g t hs M').hom ≫
      (Scheme.Modules.pullback g).map α'.hom =
    (squarePullbackIso p h g t hs M).hom ≫ (Scheme.Modules.pullback g).map α.hom

/-- Compatibility of `φ : t^* M ⟶ t^* M'` with `α` and `α'` at every factorization. -/
def Compatible {T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj M') : Prop :=
  ∀ (Z : Scheme.{u}) (g : Z ⟶ X) (h : Z ⟶ T) (hs : h ≫ t = g ≫ p),
    CompatibleAt p α α' t φ g h hs

/-- Compatibility at one factorization implies compatibility at every precomposite. -/
lemma compatibleAt_precomp {Z Z' T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj M')
    (k : Z ⟶ Z') (g' : Z' ⟶ X) (h' : Z' ⟶ T) (hs' : h' ≫ t = g' ≫ p)
    (H : CompatibleAt p α α' t φ g' h' hs') (g : Z ⟶ X) (h : Z ⟶ T)
    (hg : k ≫ g' = g) (hh : k ≫ h' = h) (hs : h ≫ t = g ≫ p) :
    CompatibleAt p α α' t φ g h hs := by
  subst hg hh
  unfold CompatibleAt at H ⊢
  have n₁ := (Scheme.Modules.pullbackComp k h').hom.naturality φ
  have n₂ := (Scheme.Modules.pullbackComp k g').hom.naturality α'.hom
  have n₃ := (Scheme.Modules.pullbackComp k g').hom.naturality α.hom
  simp only [Functor.comp_map] at n₁ n₂ n₃
  have H' := congrArg (Scheme.Modules.pullback k).map H
  simp only [Functor.map_comp] at H'
  rw [← cancel_epi ((Scheme.Modules.pullbackComp k h').hom.app
    ((Scheme.Modules.pullback t).obj M))]
  rw [← reassoc_of% n₁, ← squarePullbackIso_precomp_assoc p t k g' h' hs' hs M', ← n₂,
    reassoc_of% H', n₃, squarePullbackIso_precomp_assoc p t k g' h' hs' hs M]

/-- Compatibility at the universal factorization through `X ×_Y T` implies compatibility. -/
lemma compatible_of_universal {T : Scheme.{u}} (t : T ⟶ Y)
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj M')
    (H : CompatibleAt p α α' t φ (pullback.fst p t) (pullback.snd p t)
      pullback.condition.symm) :
    Compatible p α α' t φ := by
  intro Z g h hs
  exact compatibleAt_precomp p α α' t φ (pullback.lift g h hs.symm) _ _ _ H g h
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hs

/-- Compatibility is stable under change of base `u ≫ t = t'`. -/
lemma Compatible.change_base {T T' : Scheme.{u}} (t : T ⟶ Y) (u : T' ⟶ T) (t' : T' ⟶ Y)
    (e : u ≫ t = t')
    (φ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback t).obj M')
    (H : Compatible p α α' t φ) :
    Compatible p α α' t'
      ((compIso u t t' e M).inv ≫ (Scheme.Modules.pullback u).map φ ≫
        (compIso u t t' e M').hom) := by
  intro Z g h' hs'
  have hs : (h' ≫ u) ≫ t = g ≫ p := by rw [Category.assoc, e, hs']
  have H' := H Z g (h' ≫ u) hs
  unfold CompatibleAt at H' ⊢
  have n := (Scheme.Modules.pullbackComp h' u).hom.naturality φ
  simp only [Functor.comp_map] at n
  rw [← cancel_epi ((Scheme.Modules.pullback h').map (compIso u t t' e M).hom)]
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]
  rw [squarePullbackIso_change_base_assoc p t u t' e g h' hs' hs M', reassoc_of% n, H',
    squarePullbackIso_change_base_assoc p t u t' e g h' hs' hs M]

/-- A compatible isomorphism is unique when both modules are trivial and the base change of
`p` is an epimorphism. -/
lemma compatible_unique {T : Scheme.{u}} (t : T ⟶ Y) [Epi (pullback.snd p t)]
    (τ : (Scheme.Modules.pullback t).obj M ≅ structureModule T)
    (σ : (Scheme.Modules.pullback t).obj M' ≅ structureModule T)
    (φ ψ : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj M')
    (hφ : Compatible p α α' t φ.hom) (hψ : Compatible p α α' t ψ.hom) : φ = ψ := by
  apply pullbackIso_injective_of_trivializations (pullback.snd p t) τ σ
  apply Iso.ext
  have h₁ := hφ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  have h₂ := hψ _ (pullback.fst p t) (pullback.snd p t) pullback.condition.symm
  unfold CompatibleAt at h₁ h₂
  rw [← h₂] at h₁
  simp only [Functor.mapIso_hom]
  exact (cancel_mono ((squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
    pullback.condition.symm M') ≪≫
      (Scheme.Modules.pullback (pullback.fst p t)).mapIso α').hom).mp
    (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using h₁)

/-- Equal transported automorphisms make the quotient of the two trivializations
compatible with the canonical comparisons. -/
lemma compatible_of_equalCompositeUnitAut_eq {U : Scheme.{u}} (a b : U ⟶ X)
    (h : a ≫ p = b ≫ p)
    (heq : equalCompositeUnitAut p a b h α = equalCompositeUnitAut p a b h α') :
    (Scheme.Modules.pullback a).map (α ≪≫ α'.symm).hom ≫
        (equalCompositeIso p a b h M').hom =
      (equalCompositeIso p a b h M).hom ≫ (Scheme.Modules.pullback b).map (α ≪≫ α'.symm).hom := by
  have E := congrArg Iso.hom heq
  simp only [equalCompositeUnitAut_hom, cancel_epi] at E
  have E' : (Scheme.Modules.pullback a).map α.inv ≫ (equalCompositeIso p a b h M).hom ≫
        (Scheme.Modules.pullback b).map α.hom =
      (Scheme.Modules.pullback a).map α'.inv ≫ (equalCompositeIso p a b h M').hom ≫
        (Scheme.Modules.pullback b).map α'.hom := by
    simpa only [Category.assoc] using
      (cancel_mono (pullbackUnitIso b).hom).mp (by simpa only [Category.assoc] using E)
  rw [← cancel_epi ((Scheme.Modules.pullback a).map α.inv),
    ← cancel_mono ((Scheme.Modules.pullback b).map α'.hom)]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id_assoc, Iso.map_inv_hom_id, Category.comp_id]
  exact E'.symm

/-- Existence of a compatible isomorphism over a base on which both modules are trivial. -/
lemma exists_compatible {T : Scheme.{u}} (t : T ⟶ Y) [QuasiCompact p] [Flat p]
    [Surjective p]
    (haut : ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
      equalCompositeUnitAut p a b h α = equalCompositeUnitAut p a b h α')
    (τ : (Scheme.Modules.pullback t).obj M ≅ structureModule T)
    (σ : (Scheme.Modules.pullback t).obj M' ≅ structureModule T) :
    ∃ φ : (Scheme.Modules.pullback t).obj M ≅ (Scheme.Modules.pullback t).obj M',
      Compatible p α α' t φ.hom := by
  let β := squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
      pullback.condition.symm M ≪≫ (Scheme.Modules.pullback (pullback.fst p t)).mapIso α ≪≫
        pullbackUnitIso (pullback.fst p t)
  let β' := squarePullbackIso p (pullback.snd p t) (pullback.fst p t) t
      pullback.condition.symm M' ≪≫ (Scheme.Modules.pullback (pullback.fst p t)).mapIso α' ≪≫
        pullbackUnitIso (pullback.fst p t)
  have hβ : ∀ (U : Scheme.{u}) (a b : U ⟶ pullback p t)
      (h : a ≫ pullback.snd p t = b ≫ pullback.snd p t),
      equalCompositeUnitAut (pullback.snd p t) a b h β =
        equalCompositeUnitAut (pullback.snd p t) a b h β' := by
    intro U a b h
    have h' : (a ≫ pullback.fst p t) ≫ p = (b ≫ pullback.fst p t) ≫ p := by
      simp only [Category.assoc, pullback.condition, reassoc_of% h]
    rw [equalCompositeUnitAut_square p (pullback.snd p t) (pullback.fst p t) t
        pullback.condition.symm α a b h h',
      equalCompositeUnitAut_square p (pullback.snd p t) (pullback.fst p t) t
        pullback.condition.symm α' a b h h', haut]
  obtain ⟨φ, hφ, -⟩ := compatibleIsoDescent_of_trivializations (pullback.snd p t) τ σ
    (β ≪≫ β'.symm)
    (fun U a b h ↦ compatible_of_equalCompositeUnitAut_eq (pullback.snd p t) β β' a b h
      (hβ U a b h))
  refine ⟨φ, compatible_of_universal p α α' t φ.hom ?_⟩
  unfold CompatibleAt
  have hφ' := congrArg Iso.hom hφ
  simp only [Functor.mapIso_hom] at hφ'
  rw [hφ']
  simp [β, β']

end Compatible

section Cover

/-- Pullback of a trivial module along any morphism is trivial. -/
lemma nonempty_trivial_change_base {Y T T' : Scheme.{u}} {N : Y.Modules} (t : T ⟶ Y)
    (u : T' ⟶ T) (t' : T' ⟶ Y) (e : u ≫ t = t')
    (h : Nonempty ((Scheme.Modules.pullback t).obj N ≅ structureModule T)) :
    Nonempty ((Scheme.Modules.pullback t').obj N ≅ structureModule T') := by
  obtain ⟨τ⟩ := h
  exact ⟨(compIso u t t' e N).symm ≪≫ (Scheme.Modules.pullback u).mapIso τ ≪≫
    pullbackUnitIso u⟩

/-- A line bundle is trivial on every open inside its chosen trivializing neighborhood. -/
lemma nonempty_trivial_of_le {Y : Scheme.{u}} (L : LineBundle Y) (y : Y) (V : Y.Opens)
    (hV : V ≤ L.trivializingOpen y) :
    Nonempty ((Scheme.Modules.pullback V.ι).obj L.obj ≅ structureModule V) := by
  refine nonempty_trivial_change_base (L.trivializingOpen y).ι (Y.homOfLE hV) V.ι
    (Y.homOfLE_ι hV) ⟨?_⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback (L.trivializingOpen y).ι).app L.obj).symm ≪≫
    L.localTrivialization y

end Cover

/-- Unique gluing of module morphisms on open covers implies descent uniqueness for line
bundles with trivialized pullback. -/
theorem uniqueness_of_homGluing (hglue : OpenCoverHomGluingStatement.{u}) :
    UnitCocycleDescentUniquenessStatement.{u} := by
  intro X Y p hpaff hpflat hpsurj L L' α α' hscalar
  have := hpaff
  have := hpflat
  have := hpsurj
  have haut : ∀ (U : Scheme.{u}) (a b : U ⟶ X) (h : a ≫ p = b ≫ p),
      equalCompositeUnitAut p a b h α = equalCompositeUnitAut p a b h α' :=
    fun U a b h ↦ structureAutScalar_injective (hscalar U a b h)
  let V : Y → Y.Opens := fun y ↦ L.trivializingOpen y ⊓ L'.trivializingOpen y
  have hV : TopologicalSpace.IsOpenCover V := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun y _ ↦ ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨y, ⟨L.mem_trivializingOpen y, L'.mem_trivializingOpen y⟩⟩
  let 𝒰 := Y.openCoverOfIsOpenCover V hV
  have hL : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj L.obj ≅
      structureModule (𝒰.X i)) :=
    fun i ↦ nonempty_trivial_of_le L i (V i) inf_le_left
  have hL' : ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj L'.obj ≅
      structureModule (𝒰.X i)) :=
    fun i ↦ nonempty_trivial_of_le L' i (V i) inf_le_right
  have hE : ∀ i, ∃ φ : (Scheme.Modules.pullback (𝒰.f i)).obj L.obj ≅
      (Scheme.Modules.pullback (𝒰.f i)).obj L'.obj, Compatible p α α' (𝒰.f i) φ.hom :=
    fun i ↦ exists_compatible p α α' (𝒰.f i) haut (hL i).some (hL' i).some
  choose E hEc using hE
  obtain ⟨E₀, -, -⟩ := openCoverIsoGluing_of_homGluing hglue Y 𝒰 L.obj L'.obj E (by
    intro i j
    let w := pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i
    have hw : pullback.snd (𝒰.f i) (𝒰.f j) ≫ 𝒰.f j = w := pullback.condition.symm
    have h₁ := Compatible.change_base p α α' (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j)) w rfl
      _ (hEc i)
    have h₂ := Compatible.change_base p α α' (𝒰.f j) (pullback.snd (𝒰.f i) (𝒰.f j)) w hw
      _ (hEc j)
    have heq := compatible_unique p α α' w
      (nonempty_trivial_change_base (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j)) w rfl
        (hL i)).some
      (nonempty_trivial_change_base (𝒰.f i) (pullback.fst (𝒰.f i) (𝒰.f j)) w rfl
        (hL' i)).some
      ((compIso _ _ w rfl L.obj).symm ≪≫
        (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).mapIso (E i) ≪≫
          compIso _ _ w rfl L'.obj)
      ((compIso _ _ w hw L.obj).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).mapIso (E j) ≪≫
          compIso _ _ w hw L'.obj)
      (by simpa using h₁) (by simpa using h₂)
    have heq' := congrArg Iso.hom heq
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at heq'
    rw [squarePullbackIso_hom_eq_compIso _ _ _ _ _ w rfl hw,
      squarePullbackIso_hom_eq_compIso _ _ _ _ _ w rfl hw]
    rw [← cancel_epi (compIso _ _ w rfl L.obj).inv,
      ← cancel_mono (compIso _ _ w hw L'.obj).hom]
    simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
      using heq')
  exact ⟨ObjectProperty.isoMk _ E₀⟩

end Langlands.Scheme.Modules.UnitCocycleDescentUniqueness

namespace Langlands.Scheme.Modules

/-- Faithfully flat descent of isomorphisms for line bundles whose pullbacks are trivialized
with equal descent cocycles. -/
theorem unitCocycleDescentUniqueness : UnitCocycleDescentUniquenessStatement.{u} :=
  UnitCocycleDescentUniqueness.uniqueness_of_homGluing OpenCoverHomGluing.openCoverHomGluing

end Langlands.Scheme.Modules
