import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteActionChartDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpecFieldPoints
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation

/-! # Affine étale charts from finite group actions with a fixed point

Let a finite group `G` act on a separated scheme `Z` over `S`, freely on points valued in
nonempty schemes, and let `t : h_Z → X` be an invariant étale map to an algebraic space.
Given an equivariant map `z : Λ → Z` from a one-point scheme with a `G`-action, the
translates of an affine open neighbourhood of the image point intersect in a `G`-stable
affine open `U`. The quotient `M` of `U` by `G` is affine, `t` descends to an étale map
`h_M → X`, and `z` induces an invariant point of `M`.

The diagonal action on a fibre product `Y ×_S Λ` is free when the action on `Λ` is, and
the Galois group of `K/k` acts freely on `Spec K` over `Spec k`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Langlands.AlgebraicGeometry.Picard.DualNumberDouble (specOverMap specOverMap_left)

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An action of a group on a scheme over `S` by morphisms over `S`, written in the order
of composition: `act g ≫ act h = act (g * h)`. -/
structure OverAction (G : Type u) [Group G] (Y : Over S) where
  /-- The morphism by which an element acts. -/
  act : G → (Y ⟶ Y)
  one : act 1 = 𝟙 Y
  mul : ∀ g h, act g ≫ act h = act (g * h)

namespace OverAction

variable {G : Type u} [Group G]

section Basic

variable {Y : Over S} (ρ : OverAction G Y)

/-- Freeness on points valued in nonempty schemes. -/
def IsFree : Prop :=
  ∀ {T : Scheme.{u}} [Nonempty T] (a : T ⟶ Y.left),
    Function.Injective fun g => a ≫ (ρ.act g).left

@[reassoc]
theorem act_left_comp (g h : G) :
    (ρ.act g).left ≫ (ρ.act h).left = (ρ.act (g * h)).left := by
  rw [← Over.comp_left, ρ.mul]

instance (g : G) : IsIso (ρ.act g).left :=
  ⟨⟨(ρ.act g⁻¹).left, by rw [act_left_comp, mul_inv_cancel, ρ.one, Over.id_left],
    by rw [act_left_comp, inv_mul_cancel, ρ.one, Over.id_left]⟩⟩

end Basic

section Product

variable {Y Λ : Over S}

/-- The fibre product over `S`, whose underlying scheme is the scheme pullback. -/
def prodOver (Y Λ : Over S) : Over S :=
  Over.mk (pullback.snd Y.hom Λ.hom ≫ Λ.hom)

/-- The first projection of the fibre product. -/
def prodFst : prodOver Y Λ ⟶ Y :=
  Over.homMk (pullback.fst Y.hom Λ.hom) pullback.condition

/-- The second projection of the fibre product. -/
def prodSnd : prodOver Y Λ ⟶ Λ :=
  Over.homMk (pullback.snd Y.hom Λ.hom) rfl

@[simp] theorem prodFst_left : (prodFst : prodOver Y Λ ⟶ Y).left = pullback.fst Y.hom Λ.hom :=
  rfl

@[simp] theorem prodSnd_left : (prodSnd : prodOver Y Λ ⟶ Λ).left = pullback.snd Y.hom Λ.hom :=
  rfl

/-- The point of the fibre product with given projections. -/
def prodLift {T : Over S} (y : T ⟶ Y) (l : T ⟶ Λ) : T ⟶ prodOver Y Λ :=
  Over.homMk (pullback.lift y.left l.left ((Over.w y).trans (Over.w l).symm)) (by
    change pullback.lift _ _ _ ≫ pullback.snd Y.hom Λ.hom ≫ Λ.hom = T.hom
    rw [pullback.lift_snd_assoc, Over.w])

@[reassoc (attr := simp)]
theorem prodLift_fst {T : Over S} (y : T ⟶ Y) (l : T ⟶ Λ) : prodLift y l ≫ prodFst = y :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

@[reassoc (attr := simp)]
theorem prodLift_snd {T : Over S} (y : T ⟶ Y) (l : T ⟶ Λ) : prodLift y l ≫ prodSnd = l :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

theorem prod_hom_ext {T : Over S} {f f' : T ⟶ prodOver Y Λ}
    (h₁ : f ≫ prodFst = f' ≫ prodFst) (h₂ : f ≫ prodSnd = f' ≫ prodSnd) : f = f' :=
  Over.OverMorphism.ext (pullback.hom_ext (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂))

instance [Etale Λ.hom] : Etale (prodFst : prodOver Y Λ ⟶ Y).left :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback Y.hom Λ.hom).flip ‹_›

/-- The diagonal action on the fibre product. -/
def prod (ρ : OverAction G Y) (σ : OverAction G Λ) : OverAction G (prodOver Y Λ) where
  act g := prodLift (prodFst ≫ ρ.act g) (prodSnd ≫ σ.act g)
  one := prod_hom_ext (by simp [ρ.one]) (by simp [σ.one])
  mul g h := prod_hom_ext (by simp [← ρ.mul]) (by simp [← σ.mul])

variable (ρ : OverAction G Y) (σ : OverAction G Λ)

@[reassoc (attr := simp)]
theorem prod_act_fst (g : G) : (ρ.prod σ).act g ≫ prodFst = prodFst ≫ ρ.act g :=
  prodLift_fst _ _

@[reassoc (attr := simp)]
theorem prod_act_snd (g : G) : (ρ.prod σ).act g ≫ prodSnd = prodSnd ≫ σ.act g :=
  prodLift_snd _ _

/-- The diagonal action is free when the action on the second factor is. -/
theorem prod_isFree (hσ : σ.IsFree) : (ρ.prod σ).IsFree := by
  intro T _ a g h hgh
  apply hσ (a ≫ (prodSnd : prodOver Y Λ ⟶ Λ).left)
  have e : ∀ g, ((ρ.prod σ).act g).left ≫ (prodSnd : prodOver Y Λ ⟶ Λ).left =
      (prodSnd : prodOver Y Λ ⟶ Λ).left ≫ (σ.act g).left := fun g =>
    congrArg CommaMorphism.left (prod_act_snd ρ σ g)
  have := congrArg (· ≫ (prodSnd : prodOver Y Λ ⟶ Λ).left) hgh
  simp only [Category.assoc, e] at this
  simpa only [Category.assoc] using this

end Product

section Stable

variable [Finite G] {Z : Over S} (τ : OverAction G Z)

/-- The intersection of the translates of an open. -/
def orbitInf (U : Z.left.Opens) : Z.left.Opens :=
  ⨅ g, (τ.act g).left ⁻¹ᵁ U

theorem mem_orbitInf {U : Z.left.Opens} {x : Z.left} :
    x ∈ τ.orbitInf U ↔ ∀ g, (τ.act g).left x ∈ U := by
  rw [orbitInf, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  rfl

theorem preimage_orbitInf (U : Z.left.Opens) (h : G) :
    (τ.act h).left ⁻¹ᵁ τ.orbitInf U = τ.orbitInf U := by
  refine SetLike.ext fun x => ?_
  rw [Scheme.Hom.mem_preimage, mem_orbitInf, mem_orbitInf]
  have e : ∀ g, (τ.act g).left ((τ.act h).left x) = (τ.act (h * g)).left x := fun g => by
    rw [← Scheme.Hom.comp_apply, act_left_comp]
  simp only [e]
  constructor
  · intro H g
    simpa only [mul_inv_cancel_left] using H (h⁻¹ * g)
  · intro H g
    exact H (h * g)

theorem isAffineOpen_orbitInf [Z.left.IsSeparated] {U : Z.left.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (τ.orbitInf U) :=
  IsAffineOpen.iInf fun _ => hU.preimage_of_isIso _

end Stable

section Restrict

variable {Z : Over S}

/-- An open of a scheme over `S`, as a scheme over `S`. -/
def resOver (U : Z.left.Opens) : Over S :=
  Over.mk (U.ι ≫ Z.hom)

/-- The inclusion of an open over `S`. -/
def resOverι (U : Z.left.Opens) : resOver U ⟶ Z :=
  Over.homMk U.ι rfl

@[simp] theorem resOverι_left (U : Z.left.Opens) : (resOverι U).left = U.ι :=
  rfl

instance (U : Z.left.Opens) : _root_.AlgebraicGeometry.IsOpenImmersion (resOverι U).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion U.ι)

variable (τ : OverAction G Z) (U : Z.left.Opens) (hU : ∀ g, (τ.act g).left ⁻¹ᵁ U = U)

/-- The action on a stable open. -/
def resAct (g : G) : (resOver U).left ⟶ (resOver U).left :=
  (τ.act g).left.resLE U U (hU g).ge

@[reassoc (attr := simp)]
theorem resAct_ι (g : G) :
    τ.resAct U hU g ≫ (resOverι U).left = (resOverι U).left ≫ (τ.act g).left :=
  Scheme.Hom.resLE_comp_ι _ _

theorem resAct_one : τ.resAct U hU 1 = 𝟙 _ := by
  rw [← cancel_mono (resOverι U).left, resAct_ι, τ.one, Over.id_left, Category.id_comp,
    Category.comp_id]

theorem resAct_mul (g h : G) :
    τ.resAct U hU g ≫ τ.resAct U hU h = τ.resAct U hU (g * h) := by
  rw [← cancel_mono (resOverι U).left, Category.assoc, resAct_ι, resAct_ι_assoc, resAct_ι,
    act_left_comp]

/-- The restriction of a free action to a stable open, as a finite free scheme action. -/
def restrict (hfree : τ.IsFree) : FiniteFreeSchemeAction G (resOver U).left where
  act g :=
    { hom := τ.resAct U hU g
      inv := τ.resAct U hU g⁻¹
      hom_inv_id := by rw [resAct_mul, mul_inv_cancel, resAct_one]
      inv_hom_id := by rw [resAct_mul, inv_mul_cancel, resAct_one] }
  one := τ.resAct_one U hU
  mul := τ.resAct_mul U hU
  free {T} _ a g h hgh := hfree (a ≫ (resOverι U).left) (by
    have := congrArg (· ≫ (resOverι U).left) hgh
    simp only [Category.assoc, resAct_ι] at this
    simpa only [Category.assoc] using this)

variable (hfree : τ.IsFree)

@[simp] theorem restrict_act_hom (g : G) :
    ((τ.restrict U hU hfree).act g).hom = τ.resAct U hU g :=
  rfl

theorem restrict_over (g : G) :
    ((τ.restrict U hU hfree).act g).hom ≫ (resOver U).hom = (resOver U).hom := by
  change τ.resAct U hU g ≫ (resOverι U).left ≫ Z.hom = (resOverι U).left ≫ Z.hom
  rw [resAct_ι_assoc, Over.w]

theorem actOver_resOverι (g : G) :
    FiniteActionChart.actOver (τ.restrict U hU hfree) (τ.restrict_over U hU hfree) g ≫
      resOverι U = resOverι U ≫ τ.act g :=
  Over.OverMorphism.ext (τ.resAct_ι U hU g)

include hfree in
/-- An invariant étale map from `Z` to an algebraic space descends, on a stable affine
open, to an étale map from the affine quotient. -/
theorem exists_quotient_chart [Finite G] (X : AlgebraicSpace S) [IsAffine (resOver U).left]
    (t : (schemeYoneda S).obj Z ⟶ X.presheaf) (ht : IsEtale t)
    (hinv : ∀ g, (schemeYoneda S).map (τ.act g) ≫ t = t) :
    ∃ (M : Over S) (q : resOver U ⟶ M) (tM : (schemeYoneda S).obj M ⟶ X.presheaf),
      IsAffine M.left ∧ IsEtale tM ∧ (∀ g, τ.resAct U hU g ≫ q.left = q.left) ∧
        (schemeYoneda S).map q ≫ tM = (schemeYoneda S).map (resOverι U) ≫ t := by
  have hinvA : ∀ g, (schemeYoneda S).map
      (FiniteActionChart.actOver (τ.restrict U hU hfree) (τ.restrict_over U hU hfree) g) ≫
        (schemeYoneda S).map (resOverι U) ≫ t = (schemeYoneda S).map (resOverι U) ≫ t := by
    intro g
    rw [← Functor.map_comp_assoc, τ.actOver_resOverι U hU hfree g, Functor.map_comp_assoc,
      hinv]
  obtain ⟨tM, htM⟩ := FiniteActionChart.exists_desc (A := resOver U) (τ.restrict U hU hfree)
    (τ.restrict_over U hU hfree) (τ.restrict U hU hfree).quotient X.toSheaf
    ((schemeYoneda S).map (resOverι U) ≫ t) hinvA
  refine ⟨_, FiniteActionChart.quotientMapOver (τ.restrict U hU hfree)
    (τ.restrict_over U hU hfree) (τ.restrict U hU hfree).quotient, tM,
    inferInstance, ?_, fun g => (τ.restrict U hU hfree).quotient.invariant g, htM⟩
  apply isEtale_of_finiteEtale_comp X.hasRepresentableDiagonal
    (FiniteActionChart.quotientMapOver (τ.restrict U hU hfree) (τ.restrict_over U hU hfree)
      (τ.restrict U hU hfree).quotient)
  rw [htM]
  exact IsEtale.comp (isEtale_map _ (inferInstanceAs (Etale U.ι))) ht

end Restrict

/-- An invariant étale map from a separated scheme with a free action of a finite group, and
an equivariant point of a one-point scheme, give an affine scheme with an étale map to the
space and an invariant point lifting the given one. -/
theorem exists_affine_chart_of_point [Finite G] (X : AlgebraicSpace S) {Z Λ : Over S}
    (τ : OverAction G Z) (σ : OverAction G Λ) (hfree : τ.IsFree) [Z.left.IsSeparated]
    (t : (schemeYoneda S).obj Z ⟶ X.presheaf) (ht : IsEtale t)
    (hinv : ∀ g, (schemeYoneda S).map (τ.act g) ≫ t = t)
    (z : Λ ⟶ Z) (hz : ∀ g, z ≫ τ.act g = σ.act g ≫ z)
    [Nonempty Λ.left] [Subsingleton Λ.left] :
    ∃ (M : Over S) (tM : (schemeYoneda S).obj M ⟶ X.presheaf) (w : Λ ⟶ M),
      IsAffine M.left ∧ IsEtale tM ∧ (∀ g, σ.act g ≫ w = w) ∧
        (schemeYoneda S).map w ≫ tM = (schemeYoneda S).map z ≫ t := by
  obtain ⟨y⟩ := ‹Nonempty Λ.left›
  have hzg : ∀ g, z.left ≫ (τ.act g).left = (σ.act g).left ≫ z.left := fun g =>
    congrArg CommaMorphism.left (hz g)
  have hp : ∀ g, (τ.act g).left (z.left y) = z.left y := by
    intro g
    rw [← Scheme.Hom.comp_apply, hzg, Scheme.Hom.comp_apply,
      Subsingleton.elim ((σ.act g).left y) y]
  obtain ⟨U₀, hU₀, hpU₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show z.left y ∈ (⊤ : Z.left.Opens) from trivial)
  have hU := τ.preimage_orbitInf U₀
  have : IsAffine (resOver (τ.orbitInf U₀)).left := τ.isAffineOpen_orbitInf hU₀
  have hpU : z.left y ∈ τ.orbitInf U₀ := τ.mem_orbitInf.2 fun g => by rw [hp]; exact hpU₀
  obtain ⟨M, q, tM, hM, htM, hq, hqt⟩ :=
    τ.exists_quotient_chart (τ.orbitInf U₀) hU hfree X t ht hinv
  have hrange : Set.range z.left ⊆ Set.range (resOverι (τ.orbitInf U₀)).left := by
    rintro _ ⟨y', rfl⟩
    rw [Subsingleton.elim y' y]
    exact ⟨⟨z.left y, hpU⟩, Scheme.Opens.ι_apply _ _⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : Λ.left ⟶ (resOver (τ.orbitInf U₀)).left,
      z₁ ≫ (resOverι (τ.orbitInf U₀)).left = z.left :=
    ⟨_root_.AlgebraicGeometry.IsOpenImmersion.lift (resOverι (τ.orbitInf U₀)).left z.left hrange,
      _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange⟩
  let z' : Λ ⟶ resOver (τ.orbitInf U₀) := Over.homMk z₁ (by
    change z₁ ≫ (resOverι (τ.orbitInf U₀)).left ≫ Z.hom = Λ.hom
    rw [reassoc_of% hz₁, Over.w z])
  have hz' : z' ≫ resOverι (τ.orbitInf U₀) = z := Over.OverMorphism.ext hz₁
  refine ⟨M, tM, z' ≫ q, hM, htM, fun g => ?_, ?_⟩
  · have h₁ : (σ.act g).left ≫ z₁ = z₁ ≫ τ.resAct (τ.orbitInf U₀) hU g := by
      rw [← cancel_mono (resOverι (τ.orbitInf U₀)).left, Category.assoc, hz₁, Category.assoc,
        resAct_ι, reassoc_of% hz₁, hzg]
    apply Over.OverMorphism.ext
    change (σ.act g).left ≫ z₁ ≫ q.left = z₁ ≫ q.left
    rw [reassoc_of% h₁, hq]
  · rw [Functor.map_comp_assoc, hqt, ← Functor.map_comp_assoc, hz']

section SpecField

variable {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]

/-- The Galois group of `K/k` acting on `Spec K` over `Spec k`. -/
def galoisAction : OverAction (K ≃ₐ[k] K) (specOver k K) where
  act g := specOverMap g.toAlgHom
  one := specMap_id
  mul g h := (specMap_comp h.toAlgHom g.toAlgHom).symm

@[simp] theorem galoisAction_act (g : K ≃ₐ[k] K) :
    (galoisAction (k := k) (K := K)).act g = specOverMap g.toAlgHom :=
  rfl

/-- The Galois action on `Spec K` is free on points valued in nonempty schemes. -/
theorem galoisAction_isFree : (galoisAction (k := k) (K := K)).IsFree := by
  intro T _ a g h hgh
  change a ≫ Spec.map (CommRingCat.ofHom g.toAlgHom.toRingHom) =
    a ≫ Spec.map (CommRingCat.ofHom h.toAlgHom.toRingHom) at hgh
  obtain ⟨x⟩ := ‹Nonempty T›
  let χ := Spec.preimage (T.fromSpecResidueField x ≫ a)
  have hχ : Spec.map χ = T.fromSpecResidueField x ≫ a := Spec.map_preimage _
  have hcomp : CommRingCat.ofHom g.toAlgHom.toRingHom ≫ χ =
      CommRingCat.ofHom h.toAlgHom.toRingHom ≫ χ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hχ, Category.assoc, Category.assoc, hgh]
  ext c
  apply χ.hom.injective
  exact congrArg (fun φ : CommRingCat.of K ⟶ T.residueField x => φ.hom c) hcomp

instance : Subsingleton (specOver k K).left :=
  inferInstanceAs (Subsingleton (Spec (CommRingCat.of K)))

instance : Nonempty (specOver k K).left :=
  inferInstanceAs (Nonempty (Spec (CommRingCat.of K)))

instance [FiniteDimensional k K] [Algebra.IsSeparable k K] : Etale (specOver k K).hom := by
  have : Algebra.FormallyEtale k K := Algebra.FormallyEtale.of_isSeparable k K
  have : Algebra.FinitePresentation k K :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale k K := {}
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)

end SpecField

end OverAction

end Langlands.AlgebraicGeometry.AlgebraicSpace
