import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Adjoin.FG

/-! # Descending sections to a finitely generated subalgebra -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentStages

variable {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
  {X₀ X : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) (a : X ⟶ X₀)
  (f : X ⟶ Spec (CommRingCat.of A))

/-- The base change of `X₀` to the spectrum of a subalgebra `T`. -/
abbrev stage (T : Subalgebra A₀ A) : Scheme.{u} :=
  pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ T)))

/-- The first projection from the stage over `T`. -/
abbrev stageFst (T : Subalgebra A₀ A) : stage f₀ T ⟶ X₀ :=
  pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ T)))

/-- The second projection from the stage over `T`. -/
abbrev stageSnd (T : Subalgebra A₀ A) : stage f₀ T ⟶ Spec (CommRingCat.of T) :=
  pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ T)))

/-- A map to the stage over `T` compatible with both projections. -/
def IsLift (T : Subalgebra A₀ A) (c : X ⟶ stage f₀ T) : Prop :=
  c ≫ stageFst f₀ T = a ∧ c ≫ stageSnd f₀ T = f ≫ Spec.map (CommRingCat.ofHom (algebraMap T A))

/-- A section over the preimage of `W` descends: it comes from the stage over every
subalgebra containing a fixed finite set, along every compatible map. -/
def Descends (W : X₀.Opens) (x : Γ(X, a ⁻¹ᵁ W)) : Prop :=
  ∃ C : Finset A, ∀ (T : Subalgebra A₀ A), (↑C : Set A) ⊆ T →
    ∀ c : X ⟶ stage f₀ T, IsLift f₀ a f T c →
      ∃ y : Γ(stage f₀ T, stageFst f₀ T ⁻¹ᵁ W),
        ∀ e : a ⁻¹ᵁ W = c ⁻¹ᵁ (stageFst f₀ T ⁻¹ᵁ W),
          X.presheaf.map (eqToHom e).op (c.app (stageFst f₀ T ⁻¹ᵁ W) y) = x

variable {f₀ a f}

lemma Descends.add {W : X₀.Opens} {x x' : Γ(X, a ⁻¹ᵁ W)} (hx : Descends f₀ a f W x)
    (hx' : Descends f₀ a f W x') : Descends f₀ a f W (x + x') := by
  classical
  obtain ⟨C, hC⟩ := hx
  obtain ⟨C', hC'⟩ := hx'
  refine ⟨C ∪ C', fun T hT c hc => ?_⟩
  obtain ⟨y, hy⟩ := hC T (fun z hz => hT (Finset.mem_union_left _ hz)) c hc
  obtain ⟨y', hy'⟩ := hC' T (fun z hz => hT (Finset.mem_union_right _ hz)) c hc
  exact ⟨y + y', fun e => by rw [map_add, map_add, hy e, hy' e]⟩

lemma Descends.mul {W : X₀.Opens} {x x' : Γ(X, a ⁻¹ᵁ W)} (hx : Descends f₀ a f W x)
    (hx' : Descends f₀ a f W x') : Descends f₀ a f W (x * x') := by
  classical
  obtain ⟨C, hC⟩ := hx
  obtain ⟨C', hC'⟩ := hx'
  refine ⟨C ∪ C', fun T hT c hc => ?_⟩
  obtain ⟨y, hy⟩ := hC T (fun z hz => hT (Finset.mem_union_left _ hz)) c hc
  obtain ⟨y', hy'⟩ := hC' T (fun z hz => hT (Finset.mem_union_right _ hz)) c hc
  exact ⟨y * y', fun e => by rw [map_mul, map_mul, hy e, hy' e]⟩

lemma descends_appLE {W : X₀.Opens} (h : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ W) (w : Γ(X₀, W)) :
    Descends f₀ a f W (a.appLE W (a ⁻¹ᵁ W) h w) := by
  refine ⟨∅, fun T _ c ⟨hc₁, _⟩ => ?_⟩
  subst hc₁
  refine ⟨(stageFst f₀ T).app W w, fun e => ?_⟩
  rw [Scheme.Hom.comp_appLE]
  rfl

lemma appLE_congr_hom {Z Z' : Scheme.{u}} {g g' : Z ⟶ Z'} (hg : g = g') (U : Z'.Opens)
    (V : Z.Opens) (e : V ≤ g ⁻¹ᵁ U) : g.appLE U V e = g'.appLE U V (hg ▸ e) := by
  subst hg
  rfl

lemma descends_appLE_snd {W : X₀.Opens} (h : a ⁻¹ᵁ W ≤ f ⁻¹ᵁ ⊤)
    (b : Γ(Spec (CommRingCat.of A), ⊤)) :
    Descends f₀ a f W (f.appLE ⊤ (a ⁻¹ᵁ W) h b) := by
  classical
  let r : A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom b
  refine ⟨{r}, fun T hT c ⟨hc₁, hc₂⟩ => ?_⟩
  subst hc₁
  have hr : r ∈ T := hT (Finset.mem_singleton_self r)
  let t : T := ⟨r, hr⟩
  refine ⟨(stageSnd f₀ T).appLE ⊤ (stageFst f₀ T ⁻¹ᵁ W) le_top
    ((Scheme.ΓSpecIso (CommRingCat.of T)).inv t), fun e => ?_⟩
  have h1 : c.app (stageFst f₀ T ⁻¹ᵁ W) ≫ X.presheaf.map (eqToHom e).op =
      c.appLE (stageFst f₀ T ⁻¹ᵁ W) ((c ≫ stageFst f₀ T) ⁻¹ᵁ W) e.le := by
    rw [Scheme.Hom.appLE]
    congr 2
  have h2 : (stageSnd f₀ T).appLE ⊤ (stageFst f₀ T ⁻¹ᵁ W) le_top ≫
      c.appLE (stageFst f₀ T ⁻¹ᵁ W) ((c ≫ stageFst f₀ T) ⁻¹ᵁ W) e.le =
      (Spec.map (CommRingCat.ofHom (algebraMap T A))).appTop ≫
        f.appLE ⊤ ((c ≫ stageFst f₀ T) ⁻¹ᵁ W) h := by
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hc₂, Scheme.Hom.comp_appLE]
    rfl
  have h3 := ConcreteCategory.congr_hom h2 ((Scheme.ΓSpecIso (CommRingCat.of T)).inv t)
  have h4 := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap T A))) t
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h3 h4
  rw [← h4] at h3
  have h5 : (CommRingCat.ofHom (algebraMap T A)) t = r := rfl
  rw [h5, Iso.hom_inv_id_apply] at h3
  rw [← h3, ← ConcreteCategory.comp_apply, h1]

variable (f₀ a f) in
/-- Every section of the base change over the preimage of an affine open descends. -/
theorem descends (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    {W : X₀.Opens} (hW : IsAffineOpen W) (x : Γ(X, a ⁻¹ᵁ W)) : Descends f₀ a f W x := by
  have hUST : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap A₀ A)) ⁻¹ᵁ ⊤ := le_top
  have hUSX : W ≤ f₀ ⁻¹ᵁ ⊤ := le_top
  have hUY : a ⁻¹ᵁ W = a ⁻¹ᵁ W ⊓ f ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen hpb hUST hUSX hUY (isAffineOpen_top _)
    (isAffineOpen_top _) hW
  have P := (isIso_pushoutSection_iff hpb hUST hUSX hUY).mp hiso
  let t := f₀.appLE ⊤ W hUSX
  let b := (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))).appLE ⊤ ⊤ hUST
  let i := a.appLE W (a ⁻¹ᵁ W) le_rfl
  let j := f.appLE ⊤ (a ⁻¹ᵁ W) le_top
  let := t.hom.toAlgebra
  let := b.hom.toAlgebra
  let := i.hom.toAlgebra
  let := j.hom.toAlgebra
  let := (t ≫ i).hom.toAlgebra
  have : IsScalarTower Γ(Spec (CommRingCat.of A₀), ⊤) Γ(X₀, W) Γ(X, a ⁻¹ᵁ W) :=
    .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Spec (CommRingCat.of A₀), ⊤) Γ(Spec (CommRingCat.of A), ⊤)
      Γ(X, a ⁻¹ᵁ W) := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom P.w)
  have hP : Algebra.IsPushout Γ(Spec (CommRingCat.of A₀), ⊤) Γ(X₀, W)
      Γ(Spec (CommRingCat.of A), ⊤) Γ(X, a ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp P
  refine hP.out.inductionOn x ?_ ?_ ?_
  · intro s
    exact descends_appLE_snd le_top s
  · intro w n hn
    rw [Algebra.smul_def]
    exact (descends_appLE le_rfl w).mul hn
  · intro n₁ n₂ h₁ h₂
    exact h₁.add h₂

variable (f₀ a f) in
/-- Finitely many sections over preimages of affine opens descend simultaneously. -/
theorem exists_finset_forall_descends
    (hpb : IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    {κ : Type*} [Finite κ] (W : κ → X₀.Opens) (hW : ∀ j, IsAffineOpen (W j))
    (x : ∀ j, Γ(X, a ⁻¹ᵁ W j)) :
    ∃ C : Finset A, ∀ (T : Subalgebra A₀ A), (↑C : Set A) ⊆ T →
      ∀ c : X ⟶ stage f₀ T, IsLift f₀ a f T c → ∀ j,
        ∃ y : Γ(stage f₀ T, stageFst f₀ T ⁻¹ᵁ W j),
          ∀ e : a ⁻¹ᵁ W j = c ⁻¹ᵁ (stageFst f₀ T ⁻¹ᵁ W j),
            X.presheaf.map (eqToHom e).op (c.app (stageFst f₀ T ⁻¹ᵁ W j) y) = x j := by
  classical
  have := Fintype.ofFinite κ
  choose C hC using fun j => descends f₀ a f hpb (hW j) (x j)
  refine ⟨Finset.univ.biUnion C, fun T hT c hc j => hC j T (fun z hz => hT ?_) c hc⟩
  exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hz⟩

end Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentStages
