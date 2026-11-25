/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.EtaleLimitScalarSectionContinuity
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Filtered.Final

set_option linter.unusedVariables false

/-! # Canonical descended finite Čech comparison

Source: Stacks Project, Tags 09YN, 09YP and 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

private def coordinateInclusion {A : Type u} [DecidableEq A]
    (B : A → AddCommGrpCat.{u}) (t : A) : B t ⟶ AddCommGrpCat.of (∀ t, B t) :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦ Pi.single (M := fun s ↦ ↥(B s)) t x
      map_zero' := by ext s; by_cases h : s = t <;> simp [h]
      map_add' := by
        intro x y
        ext s
        by_cases h : s = t
        · subst s; simp
        · simp [h] }

private theorem product_colimit_of_scalar
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {A : Type (u + 1)} [Finite A] (D : I ⥤ AddCommGrpCat.{u + 1}) (K : Cocone D)
    (B : I → A → AddCommGrpCat.{u + 1}) (C : A → AddCommGrpCat.{u + 1})
    (eD : ∀ a, D.obj a ≅ AddCommGrpCat.of (∀ t, B a t))
    (eK : K.pt ≅ AddCommGrpCat.of (∀ t, C t))
    (ρ : ∀ {a a'}, (a ⟶ a') → ∀ t, B a t ⟶ B a' t)
    (μ : ∀ a t, B a t ⟶ C t)
    (hρ : ∀ {a a'} (b : a ⟶ a') t,
      D.map b ≫ (eD a').hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        (eD a).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ ρ b t)
    (hμ : ∀ a t,
      K.ι.app a ≫ eK.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        (eD a).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ μ a t)
    (hsurj : ∀ (t : A) (x : C t), ∃ (a : I) (z : B a t), μ a t z = x)
    (hzero : ∀ (a : I) (t : A) (z : B a t), μ a t z = 0 →
      ∃ (a' : I) (b : a ⟶ a'), ρ b t z = 0) : Nonempty (IsColimit K) := by
  classical
  have : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  let := Fintype.ofFinite A
  let p := fun a t ↦ (eD a).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)
  let q := fun t ↦ eK.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t)
  have hp (a : I) (x y : D.obj a) (h : ∀ t, p a t x = p a t y) : x = y := by
    apply (ConcreteCategory.isIso_iff_bijective (eD a).hom).mp inferInstance |>.1
    exact funext h
  have hq (x y : K.pt) (h : ∀ t, q t x = q t y) : x = y := by
    apply (ConcreteCategory.isIso_iff_bijective eK.hom).mp inferInstance |>.1
    exact funext h
  have hρ' {a a' : I} (b : a ⟶ a') (t : A) :
      D.map b ≫ p a' t = p a t ≫ ρ b t := hρ b t
  have hμ' (a : I) (t : A) : K.ι.app a ≫ q t = p a t ≫ μ a t := hμ a t
  have hμρ {a a' : I} (b : a ⟶ a') (t : A) (z : B a t) :
      μ a' t (ρ b t z) = μ a t z := by
    let inc := coordinateInclusion (B a) t ≫ (eD a).inv
    have hinc : inc ≫ p a t = 𝟙 _ := by
      dsimp [inc, p, coordinateInclusion]
      ext x
      simp
    have hw : p a t ≫ ρ b t ≫ μ a' t = p a t ≫ μ a t := by
      calc
        p a t ≫ ρ b t ≫ μ a' t = D.map b ≫ p a' t ≫ μ a' t := by
          rw [← Category.assoc, ← hρ', Category.assoc]
        _ = D.map b ≫ K.ι.app a' ≫ q t := by rw [← hμ']
        _ = K.ι.app a ≫ q t := by rw [← Category.assoc, K.w b]
        _ = p a t ≫ μ a t := hμ' a t
    have hh : ρ b t ≫ μ a' t = μ a t := by
      simpa only [← Category.assoc, hinc, Category.id_comp] using
        congrArg (fun f ↦ inc ≫ f) hw
    exact ConcreteCategory.congr_hom hh z
  let : ReflectsColimit D (forget AddCommGrpCat) :=
    reflectsColimit_of_reflectsIsomorphisms D (forget AddCommGrpCat)
  apply Nonempty.intro
  apply isColimitOfReflects (forget AddCommGrpCat)
  refine Types.FilteredColimit.isColimitOf' (D ⋙ forget _) ((forget _).mapCocone K) ?_ ?_
  · intro x
    choose a z hz using fun t ↦ hsurj t (q t x)
    obtain ⟨a', ha'⟩ := IsFiltered.sup_objs_exists (Finset.univ.image a)
    let b : ∀ t, a t ⟶ a' := fun t ↦ (ha' (Finset.mem_image_of_mem a (Finset.mem_univ t))).some
    let y : D.obj a' := (eD a').inv (fun t ↦ ρ (b t) t (z t))
    refine ⟨a', y, ?_⟩
    apply hq
    intro t
    change q t x = (K.ι.app a' ≫ q t) y
    rw [hμ']
    change q t x = μ a' t (p a' t y)
    have hy : p a' t y = ρ (b t) t (z t) := by simp [p, y]
    rw [hy, hμρ, hz]
  · intro a x y hxy
    change K.ι.app a x = K.ι.app a y at hxy
    have hz : ∀ t, μ a t (p a t (x - y)) = 0 := by
      intro t
      have ht := ConcreteCategory.congr_hom (hμ' a t) (x - y)
      change q t (K.ι.app a (x - y)) = μ a t (p a t (x - y)) at ht
      rw [← ht, map_sub, hxy, sub_self, map_zero]
    choose a' b hb using fun t ↦ hzero a t (p a t (x - y)) (hz t)
    obtain ⟨a'', f, g, hg⟩ := IsFiltered.wideSpan b
    refine ⟨a'', f, ?_⟩
    change D.map f x = D.map f y
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hp a'' _ 0
    intro t
    rw [map_zero]
    change (D.map f ≫ p a'' t) (x - y) = 0
    rw [← hg t, D.map_comp, Category.assoc]
    rw [hρ', ← Category.assoc, hρ', Category.assoc]
    change ρ (g t) t (ρ (b t) t (p a t (x - y))) = 0
    rw [hb, map_zero]

private noncomputable def piConcreteIso {T : Type u} (B : T → AddCommGrpCat.{u}) :
    (∏ᶜ B) ≅ AddCommGrpCat.of (∀ t, B t) :=
  (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone B).isLimit

@[reassoc]
private theorem piConcreteIso_hom_π {T : Type u} (B : T → AddCommGrpCat.{u}) (t : T) :
    (piConcreteIso B).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) = Pi.π B t := by
  exact (limit.isLimit _).conePointUniqueUpToIso_hom_comp
    (AddCommGrpCat.HasLimit.productLimitCone B).isLimit ⟨t⟩

private noncomputable def productSectionsIso {T : Type u}
    {B C : T → AddCommGrpCat.{u}} (e : ∀ t, B t ≅ C t) :
    (∏ᶜ B) ≅ AddCommGrpCat.of (∀ t, C t) :=
  Pi.mapIso e ≪≫ piConcreteIso C

@[reassoc]
private theorem productSectionsIso_hom_π {T : Type u}
    {B C : T → AddCommGrpCat.{u}} (e : ∀ t, B t ≅ C t) (t : T) :
    (productSectionsIso e).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
      Pi.π B t ≫ (e t).hom := by
  simp only [productSectionsIso, Iso.trans_hom, Category.assoc,
    piConcreteIso_hom_π, Pi.mapIso_hom_π]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical descended comparison cocone is colimiting.
Source: Stacks Project, Sites, Tag 09YN; Étale Cohomology, Tag 09YQ (qcqs inverse
limits); Cohomology on Sites, Tag 09YP, proof of lemma-colimit.
(blueprint: lem-weil-pbc-etale-limit-finite-cech-colimit).

Proof: Fix n and a tuple t. The qcqs scheme W₀(n,t) has affine-transition base
changes Wj(j,n,t); their limit is Wlim(n,t), by the base-change limit theorem. The
projection equations force γ and δ to be the pullback-pasting comparisons. Identify
the small étale topoi with the full affine étale models (09YQ), apply section
continuity (09YN) on affine objects: compute inverse-image sections by their
filtered later-stage presentations (09YM), insert these into the sectionwise
colimit of G, and reindex the two filtered colimits by their final common
refinements. Objects, arrows and equalities descend by the site-colimit
presentation, so the diagonal refinement yields the stage section diagram with
exactly the units followed by φ as transitions. Glue across a finite affine cover
of the qcqs nerve object. Filtered colimits commute with the finite equalizer for this
gluing, including the finite affine covers of intersections. Thus the section
cocone with transitions η followed by φ and γ inverse, and legs η followed by eG
inverse, L.ι and δ inverse, is colimiting. The tail is final, so the given hL supplies
the same colimit sheaf after restricting G to the tail. The last two hypotheses
identify, after eNj and eNlim, exactly these maps with every component of A.map and
cA.ι. The set of tuples Fin(n+1) → K is finite. Filtered colimits in abelian groups
commute with this product, so cA is colimiting in degree n. For any complex cocone,
the degreewise universal properties give unique maps into its vertex. Their
commutation with differentials follows by precomposing with all stage legs and
using the cocone laws; degreewise uniqueness proves this is a unique complex map.
Hence cA is a colimit in complexes. This proves a universal property for the
prescribed cocone, not for an arbitrary cocone sharing its objects. In a singleton
constant system with identity identifications, its degree-zero leg equation is
identity followed by L.ι; with identity L.ι it excludes a zero leg on a nonzero group.
Empty K and zero coefficients give zero products, so cause no exception. -/
theorem finite_cech_stage_data_is_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (U : c.pt.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (hV : ∀ k, CompactSpace (V k).left ∧ QuasiSeparatedSpace (V k).left)
    (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U)
    (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k) :
    let J := {j : I // i₀ ≤ j}
    let B := fun j : J ↦
      MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
    let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
    let Uj := fun j : J ↦ (B j).obj U₀
    let Vj := fun (j : J) (k : K) ↦ (B j).obj (V₀ k)
    let fj := fun (j : J) (k : K) ↦ (B j).map (f₀ k)
    let W₀ := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f₀ (t a))).left
    let pr₀ := fun (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)) ↦
      (Pi.π (fun a ↦ Over.mk (f₀ (t a))) a).left
    let Wj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦ (B j).obj (W₀ n t)
    let Wlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦ Blim.obj (W₀ n t)
    let Nj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (fj j (t a))).left
    let Nlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f (t a))).left
    let Pj := fun (j : J) (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ (F j.val).obj.obj (op (Nj j n t))
    let Plim := fun (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Nlim n t))
    ∀ (A : J ⥤ CochainComplex AddCommGrpCat.{u + 1} ℕ)
      (eA : ∀ j : J, A.obj j ≅
        (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
          ((Over.forget (Uj j)).op ⋙ (F j.val).obj))
      (cA : Cocone A)
      (eK : cA.pt ≅ (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
        ((Over.forget U).op ⋙ L.pt.obj))
      (eNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        Wj j n t ≅ Nj j n t)
      (eNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K), Wlim n t ≅ Nlim n t)
      (γ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t) ≅ Wj k n t)
      (δ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t) ≅ Wlim n t),
      (CompactSpace U₀.left ∧ QuasiSeparatedSpace U₀.left) ∧
      (∀ k, CompactSpace (V₀ k).left ∧ QuasiSeparatedSpace (V₀ k).left) ∧
      (∀ k, Blim.map (f₀ k) ≫ eU.hom = (eV k).hom ≫ f k) ∧
      (∀ j : J, Sieve.ofArrows (Vj j) (fj j) ∈
        (D.obj (op j.val)).smallEtaleTopology (Uj j)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNj j n t).hom ≫ (Pi.π (fun a ↦ Over.mk (fj j (t a))) a).left =
          (B j).map (pr₀ n t a)) ∧
      (∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNlim n t).hom ≫ (Pi.π (fun a ↦ Over.mk (f (t a))) a).left =
          Blim.map (pr₀ n t a) ≫ (eV (t a)).hom) ∧
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (γ j k a n t).hom.left ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j n t).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (δ j n t).hom.left ≫ pullback.fst (W₀ n t).hom (c.π.app (op i₀)) =
          pullback.fst (Wj j n t).hom (c.π.app (op j.val)) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)) ∧
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (A.map a).f n ≫ (eA k).hom.f n ≫
            Pi.π (Pj k n) t ≫ (F k.val).obj.map (eNj k n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
                (op (Wj j n t)) ≫
            (φ (show j.val ⟶ k.val from a)).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t))) ≫
            (F k.val).obj.map (γ j k a n t).inv.op) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (eA j).inv.f n ≫ (cA.ι.app j).f n ≫ eK.hom.f n ≫
            Pi.π (Plim n) t ≫ L.pt.obj.map (eNlim n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Wj j n t)) ≫
            (eG j.val).inv.hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            (L.ι.app j.val).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            L.pt.obj.map (δ j n t).inv.op) →
      Nonempty (IsColimit cA) := by
  classical
  dsimp only
  intro A eA cA eK eNj eNlim γ δ h
  obtain ⟨hU₀, hV₀, heV, hcover, hNj, hNlim, hγ, hδ, hA, hcA⟩ := h
  let J := {j : I // i₀ ≤ j}
  have : Nonempty J := ⟨⟨i₀, le_refl i₀⟩⟩
  have : IsDirected J (· ≤ ·) := ⟨by
    intro j k
    obtain ⟨l, hj, hk⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hj⟩, hj, hk⟩⟩
  let B := fun j : J ↦
    MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
  let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
  let W₀ := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
    (∏ᶜ fun a ↦ Over.mk (f₀ (t a))).left
  let Wj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦ (B j).obj (W₀ n t)
  let Wlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦ Blim.obj (W₀ n t)
  let : CompactSpace U₀.left := hU₀.1
  let : QuasiSeparatedSpace U₀.left := hU₀.2
  have hW (n : ℕ) (t : Fin (n + 1) → K) :
      CompactSpace (W₀ n t).left ∧ QuasiSeparatedSpace (W₀ n t).left :=
    Scheme.compactSpace_and_quasiSeparatedSpace_piObj _ (fun a ↦ hV₀ (t a))
  refine ⟨HomologicalComplex.isColimitOfEval A cA (fun n ↦ ?_)⟩
  let Nj := fun (j : J) (t : Fin (n + 1) → K) ↦
    (∏ᶜ fun a ↦ Over.mk ((B j).map (f₀ (t a)))).left
  let Nlim := fun t : Fin (n + 1) → K ↦
    (∏ᶜ fun a ↦ Over.mk (f (t a))).left
  let Pj := fun j : J ↦ fun t : Fin (n + 1) → K ↦ (F j.val).obj.obj (op (Nj j t))
  let Plim := fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Nlim t))
  let P := fun (j : J) (t : Fin (n + 1) → K) ↦
    (F j.val).obj.obj (op (Wj j n t))
  let Q := fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Wlim n t))
  let eD : ∀ j : J, (A.obj j).X n ≅ AddCommGrpCat.of (∀ t, P j t) := fun j ↦
    (HomologicalComplex.eval _ (ComplexShape.up ℕ) n).mapIso (eA j) ≪≫
      productSectionsIso (B := Pj j) (C := P j)
        (fun t ↦ (F j.val).obj.mapIso (eNj j n t).op)
  let eC : cA.pt.X n ≅ AddCommGrpCat.of (∀ t, Q t) :=
    (HomologicalComplex.eval _ (ComplexShape.up ℕ) n).mapIso eK ≪≫
      productSectionsIso (B := Plim) (C := Q)
        (fun t ↦ L.pt.obj.mapIso (eNlim n t).op)
  let ρ : ∀ {j k : J}, (j ⟶ k) → ∀ t, P j t ⟶ P k t := fun {j k} a t ↦
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
        (op (Wj j n t)) ≫
      (φ (show j.val ⟶ k.val from a)).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t))) ≫
      (F k.val).obj.map (γ j k a n t).inv.op
  let μ := fun (j : J) (t : Fin (n + 1) → K) ↦
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Wj j n t)) ≫
      (eG j.val).inv.hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t))) ≫
      (L.ι.app j.val).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t))) ≫
      L.pt.obj.map (δ j n t).inv.op
  have hs (t : Fin (n + 1) → K) :
      (∀ x : Q t, ∃ (j : J) (z : P j t), μ j t z = x) ∧
      (∀ (j : J) (z : P j t), μ j t z = 0 →
        ∃ (k : J) (a : j ⟶ k), ρ a t z = 0) := by
    let : CompactSpace (W₀ n t).left := (hW n t).1
    let : QuasiSeparatedSpace (W₀ n t).left := (hW n t).2
    exact etale_limit_scalar_sections_representatives_and_zero D c hc F φ hidentity
      hcomposition G eG hG L hL i₀ (W₀ n t)
      (fun j k a ↦ γ j k a n t) (fun j ↦ δ j n t)
      (fun j k a ↦ hγ j k a n t) (fun j ↦ hδ j n t)
  have eDp (j : J) (t : Fin (n + 1) → K) :
      (eD j).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        (eA j).hom.f n ≫ Pi.π (Pj j) t ≫ (F j.val).obj.map (eNj j n t).hom.op := by
    exact congrArg (fun z ↦ (eA j).hom.f n ≫ z)
      (productSectionsIso_hom_π (B := Pj j) (C := P j)
        (fun t ↦ (F j.val).obj.mapIso (eNj j n t).op) t)
  have eCp (t : Fin (n + 1) → K) :
      eC.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        eK.hom.f n ≫ Pi.π Plim t ≫ L.pt.obj.map (eNlim n t).hom.op := by
    exact congrArg (fun z ↦ eK.hom.f n ≫ z)
      (productSectionsIso_hom_π (B := Plim) (C := Q)
        (fun t ↦ L.pt.obj.mapIso (eNlim n t).op) t)
  have hcancel (j : J) : (eA j).hom.f n ≫ (eA j).inv.f n = 𝟙 _ := by
    change ((eA j).hom ≫ (eA j).inv).f n = _
    rw [Iso.hom_inv_id]
    rfl
  have hρ {j k : J} (a : j ⟶ k) (t : Fin (n + 1) → K) :
      (A.map a).f n ≫ (eD k).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        (eD j).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ ρ a t := by
    have hh := congrArg (fun z ↦ (eA j).hom.f n ≫ z) (hA j k a n t)
    simp only [← Category.assoc, hcancel, Category.id_comp] at hh
    rw [eDp k t, reassoc_of% (eDp j t)]
    simpa only [Category.assoc, ρ] using hh
  have hμ (j : J) (t : Fin (n + 1) → K) :
      (cA.ι.app j).f n ≫ eC.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
        (eD j).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ μ j t := by
    have hh := congrArg (fun z ↦ (eA j).hom.f n ≫ z) (hcA j n t)
    simp only [← Category.assoc, hcancel, Category.id_comp] at hh
    change (((cA.ι.app j).f n ≫ eK.hom.f n) ≫ Pi.π Plim t ≫
      L.pt.obj.map (eNlim n t).hom.op) =
      (((eA j).hom.f n ≫ Pi.π (Pj j) t) ≫
        (F j.val).obj.map (eNj j n t).hom.op) ≫ μ j t at hh
    calc
      (cA.ι.app j).f n ≫ eC.hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) =
          (cA.ι.app j).f n ≫ eK.hom.f n ≫ Pi.π Plim t ≫
            L.pt.obj.map (eNlim n t).hom.op := by rw [eCp t]
      _ = (eD j).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ t) ≫ μ j t := by
        have hd := congrArg (fun z ↦ z ≫ μ j t) (eDp j t)
        exact hh.trans hd.symm
  exact Classical.choice (product_colimit_of_scalar
    (A ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) n)
    ((HomologicalComplex.eval _ (ComplexShape.up ℕ) n).mapCocone cA)
    P Q eD eC ρ μ (fun a t ↦ hρ a t) hμ
    (fun t ↦ (hs t).1) (fun j t ↦ (hs t).2 j))


end AlgebraicGeometry.Etale
