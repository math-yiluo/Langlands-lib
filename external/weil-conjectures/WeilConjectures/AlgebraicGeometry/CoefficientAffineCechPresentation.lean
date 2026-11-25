/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechSystem
import WeilConjectures.AlgebraicGeometry.CechNervePresentationConstruction

/-! # Geometric presentations of coefficient-site finite Čech nerves

The data in this file are independent of a coefficient ring, a sheaf, and a cohomological
 degree. Source: Stacks Project, Tag 099U, the two finite-cover limit reductions.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem exists_surjective_presentation
    {Y : Scheme.{u}} {A B : Y.AffineProEt} (q : A ⟶ B) [Surjective q.left] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (pA : RelativeLimitPresentation I (Scheme.AffineEtale.toAffineProEt Y) A)
      (pB : RelativeLimitPresentation I (Scheme.AffineEtale.toAffineProEt Y) B)
      (f : pA.Hom pB), f.map = q ∧
      ∀ i, Sieve.generate (Presieve.singleton (f.natTrans.app i)) ∈
        Scheme.AffineEtale.topology Y (pB.diag.obj i) := by
  have hrel : PreZeroHypercover.IsRelativelyPresentable.{u}
      (Scheme.AffineEtale.toAffineProEt Y) (Scheme.AffineEtale.topology Y)
      (Presieve.singleton q).preZeroHypercover := by
    apply Scheme.AffineProEt.singleton_inf_le_relativelyPresentable
    refine ⟨⟨A, q, rfl⟩, ?_⟩
    rw [MorphismProperty.singleton_mem_precoverage_iff]
    infer_instance
  obtain ⟨I, _, _, p, hp⟩ := hrel
  let a₀ : (Presieve.singleton q).preZeroHypercover.I₀ :=
    ⟨⟨A, q⟩, Presieve.singleton.mk⟩
  have ha (a : (Presieve.singleton q).preZeroHypercover.I₀) : a = a₀ := by
    rcases a with ⟨⟨Z, t⟩, ht⟩
    cases ht
    rfl
  refine ⟨I, inferInstance, inferInstance, p.pres₀ a₀, p.pres, p.f a₀, p.hf a₀, ?_⟩
  intro i
  have he : (p.preZeroHypercover i).sieve₀ =
      Sieve.generate (Presieve.singleton ((p.f a₀).natTrans.app i)) := by
    apply congrArg Sieve.generate
    apply le_antisymm
    · rintro Z t ⟨a⟩
      obtain rfl := ha a
      exact Presieve.singleton.mk
    · rintro Z t ⟨⟩
      exact ⟨a₀⟩
  rw [← he]
  exact hp i

private theorem coverPresentation
    (Y : Scheme.{u})
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ a, proAffineEtale (U a).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (P : (finiteCover U).RelativeLimitPresentation (Scheme.toProEt Y) I),
      (∀ i, Sieve.ofArrows (fun a ↦ (P.pres₀ a).diag.obj i)
        (fun a ↦ (P.f a).natTrans.app i) ∈ Y.smallEtaleTopology (P.pres.diag.obj i)) ∧
      (∀ i, IsAffine (P.pres.diag.obj i).left) ∧
      (∀ i a, IsAffine ((P.pres₀ a).diag.obj i).left) ∧
      Nonempty (IsLimit ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone P.pres.cone)) ∧
      ∀ a, Nonempty (IsLimit
        ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (P.pres₀ a).cone)) := by
  classical
  let B : Y.AffineProEt := Scheme.AffineProEt.mk V.hom hV
  let A (a : Fin n) : Y.AffineProEt :=
    Scheme.AffineProEt.mk (U a).left.hom (hU a)
  let f (a : Fin n) : A a ⟶ B :=
    MorphismProperty.Over.homMk (U a).hom.left (U a).hom.w trivial
  have hcov : Sieve.ofArrows A f ∈ Scheme.AffineProEt.topology Y B := by
    rw [← Functor.functorPushforward_mem_iff _ (Scheme.ProEt.topology Y)
      (Scheme.AffineProEt.toProEt Y), Sieve.functorPushforward_ofArrows]
    exact hcover
  have hsurj : ∀ x : B.left, ∃ a, x ∈ Set.range ((f a).left.base) := by
    obtain ⟨ι, _, Z, g, hg, hs⟩ :=
      Scheme.AffineProEt.exists_finite_jointly_surjective_of_mem_topology hcov
    intro x
    obtain ⟨i, z, hz⟩ := hs x
    obtain ⟨Q, r, t, ⟨a⟩, ht⟩ := hg i
    refine ⟨a, r.left.base z, ?_⟩
    rw [← hz, ← ht]
    rfl
  obtain ⟨W, q, j, hq, hjq, hj, hjcov⟩ :=
    Scheme.AffineProEt.exists_surjective_factorization
      (fun a : ULift.{u} (Fin n) ↦ A a.down) (fun a ↦ f a.down) (by
        intro x
        obtain ⟨a, z, hz⟩ := hsurj x
        exact ⟨ULift.up a, z, hz⟩)
  let : Surjective q.left := hq
  obtain ⟨I, _, _, pW, pB, pq, hpq, hqcov⟩ := exists_surjective_presentation q
  let j' (a : Fin n) : A a ⟶ W := j (ULift.up a)
  let cov : W.left.OpenCover := by
    refine ⟨⟨Fin n, fun a ↦ (A a).left, fun a ↦ (j' a).left⟩, ?_⟩
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_, fun a ↦ hj (ULift.up a)⟩
    intro x
    obtain ⟨a, z, hz⟩ := hjcov x
    exact ⟨a.down, z, hz⟩
  have : ∀ a, IsAffine (cov.X a) := fun a ↦ by
    change IsAffine (A a).left
    infer_instance
  have : Finite cov.I₀ := inferInstanceAs (Finite (Fin n))
  let F := Scheme.AffineEtale.toScheme Y
  let R := Scheme.AffineProEt.toScheme Y
  have : ∀ i, IsAffine ((pW.diag ⋙ F).obj i) := fun i ↦ by
    change IsAffine ((Scheme.AffineEtale.Spec Y).obj (pW.diag.obj i)).left
    rw [Scheme.AffineEtale.Spec_obj_left]
    infer_instance
  let x := R.mapCone pW.cone
  obtain ⟨i, rings, v, hv, g, hg⟩ := cov.exists_of_isCofiltered_of_finite
    (pW.diag ⋙ F) x (isLimitOfPreserves R pW.isLimit)
  have (a : Fin n) : IsOpenImmersion (v a) := hv.right ⟨a⟩
  have : Etale (pW.diag.obj i).hom := (pW.diag.obj i).prop
  let E (a : Fin n) : Y.AffineEtale := Scheme.AffineEtale.mk
    (v a ≫ (pW.diag.obj i).hom)
  let v' (a : Fin n) : E a ⟶ pW.diag.obj i :=
    MorphismProperty.CostructuredArrow.homMk (Spec.preimage (v a)).op trivial (by simp [E])
  let g' (a : Fin n) : A a ⟶ (Scheme.AffineEtale.toAffineProEt Y).obj (E a) := by
    refine MorphismProperty.Over.homMk (g a) ?_ trivial
    have h1 := CostructuredArrow.w (j' a).toCommaMorphism
    dsimp at h1
    have h2 := CostructuredArrow.w (pW.π.app i).toCommaMorphism
    dsimp at h2
    change (pW.π.app i).left ≫ (pW.diag.obj i).hom = W.hom at h2
    change (j' a).left ≫ W.hom = (A a).hom at h1
    change g a ≫ (v a ≫ (pW.diag.obj i).hom) = (A a).hom
    rw [(hg a).w_assoc]
    change (j' a).left ≫ (pW.π.app i).left ≫ (pW.diag.obj i).hom = (A a).hom
    rw [h2, h1]
  have hpb (a : Fin n) : IsPullback (g' a) (j' a)
      ((Scheme.AffineEtale.toAffineProEt Y).map (v' a)) (pW.π.app i) := by
    refine IsPullback.of_map_of_faithful R ?_
    simpa [R, v', g', x, cov, E] using hg a
  let pA (a : Fin n) := pW.restrict (v' a) (A a) (g' a) (j' a) (hpb a)
  let pB' := pB.precomp (Over.forget i)
  let pq' : (pW.precomp (Over.forget i)).Hom pB' :=
    ⟨Functor.whiskerLeft (Over.forget i) pq.natTrans⟩
  let pf (a : Fin n) : (pA a).Hom pB' :=
    (pW.restrictHom (v' a) (A a) (g' a) (j' a) (hpb a)).comp pq'
  have hpf (a : Fin n) : (pf a).map = f a := by
    apply pB'.isLimit.hom_ext
    intro b
    rw [RelativeLimitPresentation.Hom.map_π]
    change (pA a).π.app b ≫ (Scheme.AffineEtale.toAffineProEt Y).map
      ((pW.restrictHom (v' a) (A a) (g' a) (j' a) (hpb a)).natTrans.app b ≫
        pq.natTrans.app b.left) = _
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc,
      ← RelativeLimitPresentation.Hom.map_π,
      RelativeLimitPresentation.restrictHom_map]
    rw [Category.assoc]
    change j' a ≫ pW.π.app b.left ≫ _ = _
    rw [← RelativeLimitPresentation.Hom.map_π, hpq, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ pB.π.app b.left) (hjq (ULift.up a))
  let peB : RelativeLimitPresentation (Over i) (Scheme.toProEt Y) V :=
    { diag := presentationDiagram pB'
      π := (presentationCone pB').π
      isLimit := isLimitOfReflects (Scheme.ProEt.forget Y)
        (isLimitOfReflects (Over.forget Y) (isLimitPresentationCone pB')) }
  let peA (a : Fin n) : RelativeLimitPresentation (Over i) (Scheme.toProEt Y) (U a).left :=
    { diag := presentationDiagram (pA a)
      π := (presentationCone (pA a)).π
      isLimit := isLimitOfReflects (Scheme.ProEt.forget Y)
        (isLimitOfReflects (Over.forget Y) (isLimitPresentationCone (pA a))) }
  let pfe (a : Fin n) : (peA a).Hom peB :=
    ⟨Functor.whiskerRight (pf a).natTrans (Scheme.AffineEtale.Spec Y)⟩
  have hpfe (a : Fin n) : (pfe a).map = (U a).hom := by
    apply peB.isLimit.hom_ext
    intro b
    rw [RelativeLimitPresentation.Hom.map_π]
    apply (Scheme.ProEt.forget Y ⋙ Over.forget Y).map_injective
    have hw := congrArg (Scheme.AffineProEt.toScheme Y).map ((pf a).map_π b)
    rw [hpf] at hw
    change ((pA a).π.app b).left ≫
      (Scheme.AffineEtale.toScheme Y).map ((pf a).natTrans.app b) =
      (f a).left ≫ (pB'.π.app b).left
    exact hw.symm
  let P : (finiteCover U).RelativeLimitPresentation (Scheme.toProEt Y) (Over i) :=
    ⟨peB, peA, pfe, hpfe⟩
  refine ⟨Over i, inferInstance, inferInstance, P, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro t
    have hQ := (Functor.functorPushforward_mem_iff
      (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology
      (Scheme.AffineEtale.Spec Y)).mpr (hqcov b.left)
    rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton,
      ← Presieve.ofArrows_pUnit.{0}] at hQ
    have hQ' := Scheme.ofArrows_mem_smallEtaleTopology_iff _ |>.mp hQ
    have ht : t ∈ ⋃ a : PUnit.{1}, Set.range
        ((Scheme.AffineEtale.Spec Y).map (pq.natTrans.app b.left)).left := by
      rw [hQ']
      trivial
    obtain ⟨_, z, hz⟩ := Set.mem_iUnion.mp ht
    have hv' := (Scheme.ofArrows_mem_precoverage_iff _).mp hv
    obtain ⟨a, w, hw⟩ := hv'.1 ((F.map (pW.diag.map b.hom)).base z)
    have H := (IsPullback.of_hasPullback (pW.diag.map b.hom) (v' a)).map F
    have hxy : (F.map (pW.diag.map b.hom)).base z = (F.map (v' a)).base w := by
      have he : F.map (v' a) = v a := by
        simp [F, v']
      rw [he]
      exact hw.symm
    obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback z w hxy
    let r := H.isoPullback.inv.base p
    have hr : (F.map (pullback.fst (pW.diag.map b.hom) (v' a))).base r = z := by
      change (H.isoPullback.inv ≫ F.map (pullback.fst _ _)).base p = z
      rw [H.isoPullback_inv_fst]
      exact hp₁
    apply Set.mem_iUnion.mpr
    refine ⟨a, r, ?_⟩
    change (F.map (pullback.fst (pW.diag.map b.hom) (v' a) ≫
      pq.natTrans.app b.left)).base r = t
    rw [CategoryTheory.Functor.map_comp]
    change (F.map (pq.natTrans.app b.left)).base
      ((F.map (pullback.fst _ _)).base r) = t
    rw [hr]
    exact hz
  · intro b
    exact inferInstanceAs (IsAffine ((presentationDiagram pB').obj b).left)
  · intro b a
    exact inferInstanceAs (IsAffine ((presentationDiagram (pA a)).obj b).left)
  · exact ⟨isLimitPresentationCone pB'⟩
  · intro a
    exact ⟨isLimitPresentationCone (pA a)⟩

section ProductTransport
universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {T : Type*} {U : C}
  {V : T → C} {f : ∀ a, V a ⟶ U} (S : SiteCechComplex V f)

private def fibreCone (p : ℕ) (t : Fin (p + 1) → T) :
    WidePullbackCone (fun k ↦ f (t k)) :=
  WidePullbackCone.mk (S.pr p t 0 ≫ f (t 0)) (S.pr p t) (S.comm p t)

private noncomputable def fibreLimit (p : ℕ) (t : Fin (p + 1) → T) :
    IsLimit (fibreCone S p t) := by
  classical
  have hu (c : WidePullbackCone (fun k ↦ f (t k))) :=
    S.universal p t c.pt c.π (fun k ↦ (c.condition k).trans (c.condition 0).symm)
  refine WidePullbackCone.IsLimit.mk _ (fun c ↦ (hu c).choose) ?_ ?_ ?_
  · intro c
    change (hu c).choose ≫ S.pr p t 0 ≫ f (t 0) = c.base
    rw [← Category.assoc, (hu c).choose_spec.1 0, c.condition]
  · intro c k
    exact (hu c).choose_spec.1 k
  · intro c b _ hb
    exact (hu c).choose_spec.2 b hb

private theorem mappedUniversal {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [PreservesFiniteLimits F]
    (p : ℕ) (t : Fin (p + 1) → T) (Z : D)
    (a : ∀ k, Z ⟶ F.obj (V (t k)))
    (ha : ∀ k, a k ≫ F.map (f (t k)) = a 0 ≫ F.map (f (t 0))) :
    ∃! b : Z ⟶ F.obj (S.W p t), ∀ k, b ≫ F.map (S.pr p t k) = a k := by
  let e : (WidePullbackShape.wideCospan U (fun k ↦ V (t k)) (fun k ↦ f (t k))) ⋙ F ≅
      WidePullbackShape.wideCospan (F.obj U) (fun k ↦ F.obj (V (t k)))
        (fun k ↦ F.map (f (t k))) :=
    NatIso.ofComponents (fun z ↦ by cases z <;> exact Iso.refl _) (by
      intro i j h
      cases h with
      | id =>
        cases i <;> change F.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
        all_goals rw [F.map_id]
      | term k =>
        change F.map (f (t k)) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (f (t k))
        rw [Category.comp_id, Category.id_comp])
  let c := (Cone.postcompose e.hom).obj (F.mapCone (fibreCone S p t))
  have hc : IsLimit c :=
    (IsLimit.postcomposeHomEquiv e _).symm (isLimitOfPreserves F (fibreLimit S p t))
  let d := WidePullbackCone.mk (a 0 ≫ F.map (f (t 0))) a ha
  let b' : Z ⟶ F.obj (S.W p t) := hc.lift d
  have hf (k : Fin (p + 1)) : b' ≫ F.map (S.pr p t k) = a k := by
    simpa [b', c, e, fibreCone, d, WidePullbackCone.mk, WidePullbackShape.mkCone]
      using hc.fac d (some k)
  refine ⟨b', hf, ?_⟩
  intro b hb
  apply hc.hom_ext
  rintro (_ | k)
  · change b ≫ (F.map (S.pr p t 0 ≫ f (t 0)) ≫ 𝟙 _) =
      b' ≫ (F.map (S.pr p t 0 ≫ f (t 0)) ≫ 𝟙 _)
    rw [Category.comp_id, F.map_comp, ← Category.assoc, ← Category.assoc, hb, hf]
  · change b ≫ (F.map (S.pr p t k) ≫ 𝟙 _) = b' ≫ (F.map (S.pr p t k) ≫ 𝟙 _)
    rw [Category.comp_id, hb, hf]

@[implicit_reducible] private def mapCech {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) [PreservesFiniteLimits F] :
    SiteCechComplex (fun t ↦ F.obj (V t)) (fun t ↦ F.map (f t)) where
  W p t := F.obj (S.W p t)
  pr p t k := F.map (S.pr p t k)
  comm p t k := by simp only [← F.map_comp, S.comm]
  universal := mappedUniversal S F
  W_zero t := congrArg F.obj (S.W_zero t)
  pr_zero t := by simp only [S.pr_zero, eqToHom_map]
  indexMap t a := F.map (S.indexMap t a)
  indexMap_pr t a k := by rw [← F.map_comp, S.indexMap_pr]

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
variable {n : ℕ} {V : Fin n → C} {f : ∀ a, V a ⟶ U}
  (S : SiteCechComplex V f) [HasFiniteLimits C]

private noncomputable def orderedIso (p : ℕ) (t : Fin (p + 1) → Fin n) :
    S.W p t ≅ (Presheaf.cechNerveObj (fun a ↦ Over.mk (f a)) t).left :=
  (fibreLimit S p t).conePointUniqueUpToIso
    (Presheaf.nerveWideConeIsLimit (fun a ↦ Over.mk (f a)) t)

private theorem orderedIso_pr (p : ℕ) (t : Fin (p + 1) → Fin n) (k : Fin (p + 1)) :
    (orderedIso S p t).hom ≫ (Pi.π (fun k ↦ Over.mk (f (t k))) k).left = S.pr p t k :=
  (fibreLimit S p t).conePointUniqueUpToIso_hom_comp
    (Presheaf.nerveWideConeIsLimit (fun a ↦ Over.mk (f a)) t) (some k)

private theorem orderedIso_index {p q : ℕ} (t : Fin (p + 1) → Fin n)
    (α : Fin (q + 1) → Fin (p + 1)) :
    S.indexMap t α ≫ (orderedIso S q (t ∘ α)).hom =
      (orderedIso S p t).hom ≫
        (Presheaf.cechNerveMap (fun a ↦ Over.mk (f a)) t α).left := by
  have hp (k : Fin (q + 1)) :
      (S.indexMap t α ≫ (orderedIso S q (t ∘ α)).hom) ≫
          (Pi.π (fun k ↦ Over.mk (f ((t ∘ α) k))) k).left =
        ((orderedIso S p t).hom ≫
          (Presheaf.cechNerveMap (fun a ↦ Over.mk (f a)) t α).left) ≫
          (Pi.π (fun k ↦ Over.mk (f ((t ∘ α) k))) k).left := by
    rw [Category.assoc, orderedIso_pr, Category.assoc, Presheaf.cechNerveMap_left_π,
      orderedIso_pr, S.indexMap_pr]
  apply Over.pi_left_hom_ext _ hp
  rw [← Over.w (Pi.π (fun k ↦ Over.mk (f ((t ∘ α) k))) 0)]
  simp only [← Category.assoc, hp]

private theorem orderedIso_inv_index {p q : ℕ} (t : Fin (p + 1) → Fin n)
    (α : Fin (q + 1) → Fin (p + 1)) :
    (orderedIso S p t).inv ≫ S.indexMap t α =
      (Presheaf.cechNerveMap (fun a ↦ Over.mk (f a)) t α).left ≫
        (orderedIso S q (t ∘ α)).inv := by
  apply (cancel_mono (orderedIso S q (t ∘ α)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [orderedIso_index, Iso.inv_hom_id_assoc]

end ProductTransport

/-- Finite affine pro-étale covers admit simultaneous affine étale covering approximations,
with scheme-limit cones on all their repeated intersections. This is a purely geometric
assertion: it says nothing about sections, injectivity, exactness, or cohomology.
Source: Stacks Project, Tag 099U, the two finite Čech limit reductions; Limits Tags
01ZM, 01ZN and 07RP for finite-presentation and covering descent.
(auxiliary; not a blueprint node).

Proof: transport the covering sieve through AsSmall.down. Factor the finite family through
its affine disjoint union, a single surjection onto U. The singleton relative-presentability
result gives compatible affine étale presentations of this surjection. Descend the finite
affine open cover of its source by Scheme.OpenCover.exists_of_isCofiltered_of_finite, and
restrict its presentations to the descended opens. Cone identities identify the resulting
member maps with the original covering arrows. Lifting points through the singleton stage
cover and its descended open cover proves that every stage family covers. This construction
does not require the ambient X to be affine.

Construct all ordered intersections using systemOfPresentation. The base and member limit
properties give the intersection limit properties by presentedNerveIsLimit. Choose normalized
SiteCechComplex structures for the étale stage covers. View each chosen intersection as a
limiting wide-pullback cone and compare it with the ordered product by its unique compatible
isomorphism. Projecting to each factor shows that these isomorphisms commute with all index
maps. Conjugate the transitions and cone projections by these isomorphisms. Transfer affineness
through the same isomorphisms and Scheme.isAffine_of_isLimit. Map the normalized complexes
through AsSmall.up, and enlarge the small index to universe u+1 by AsSmall. Whiskering by this
equivalence and transporting the diagram and vertex isomorphisms preserves the limit cones.
Empty families have no nonempty tuples and need no separate coefficient argument. -/
theorem exists_coefficient_affine_cech_presentation (X : Scheme.{u})
    (U : Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (m : ℕ) (V : Fin m → Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (f : ∀ a, V a ⟶ U)
    (hU : proAffineEtale (AsSmall.down.obj U).hom)
    (hV : ∀ a, proAffineEtale (AsSmall.down.obj (V a)).hom)
    (hc : Presieve.ofArrows V f ∈
      (Scheme.coefficientProEtaleModelTopology.{u, v} X).toPrecoverage U)
    (S : SiteCechComplex V f) :
    ∃ (J : Type (u + 1)) (_ : SmallCategory J) (_ : IsCofiltered J)
      (P : CoefficientAffineCechPresentation X S J),
      ∀ p t, Nonempty (IsLimit
        (((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt) ⋙
          Scheme.ProEt.forget X).mapCone (P.cone p t))) := by
  classical
  let B : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X := AsSmall.up
  let D : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  have : D.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse
  have : (AsSmall.up : X.Etale ⥤
      Scheme.smallModelComparisonEtaleSite.{u, v} X).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).symm.isEquivalence_inverse
  let V' : Fin m → Over (D.obj U) := fun a ↦ Over.mk (D.map (f a))
  have hcov : Sieve.ofArrows (fun a ↦ (V' a).left) (fun a ↦ (V' a).hom) ∈
      Scheme.ProEt.topology X (D.obj U) := by
    have h := (CoverPreserving.of_isContinuous D
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) (Scheme.ProEt.topology X)).cover_preserve
        (show Sieve.ofArrows V f ∈
          Scheme.coefficientProEtaleModelTopology.{u, v} X U from hc)
    rw [Sieve.functorPushforward_ofArrows] at h
    exact h
  obtain ⟨I, _, _, Q, hcov, hAff, hAff₀, hB, hA⟩ :=
    coverPresentation X (D.obj U) hU V' hV hcov
  let E := systemOfPresentation V' Q hcov hAff hAff₀
  have hE (p : ℕ) (t : Fin (p + 1) → Fin m) :=
    presentedNerveIsLimit V' Q hB.some (fun a ↦ (hA a).some) p t
  let R (i : I) : SiteCechComplex (E.T i) (E.f i) :=
    (SiteCechComplex.exists_of_covering X.smallEtaleTopology.toPrecoverage
      (show Presieve.ofArrows (E.T i) (E.f i) ∈
        X.smallEtaleTopology.toPrecoverage (E.W i) from E.covering i)).some
  let e (i : I) (p : ℕ) (t : Fin (p + 1) → Fin m) := orderedIso (R i) p t
  let e₀ (p : ℕ) (t : Fin (p + 1) → Fin m) := orderedIso (mapCech S D) p t
  let J := AsSmall.{u + 1} I
  let L : J ⥤ I := AsSmall.down
  have : L.IsEquivalence :=
    (AsSmall.equiv.{u, u, u + 1} (C := I)).isEquivalence_inverse
  let T : X.Etale ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X := AsSmall.up
  have : T.IsContinuous X.smallEtaleTopology
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).functor.IsContinuous
      X.smallEtaleTopology
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.inducedTopology
        X.smallEtaleTopology))
  have hRa (i : I) (p : ℕ) (t : Fin (p + 1) → Fin m) :
      IsAffine ((R i).W p t).left := by
    have : IsAffine ((Scheme.Etale.forget X ⋙ Over.forget X).obj
        (Presheaf.cechNerveObj (fun a ↦ Over.mk (E.f i a)) t).left) := E.affine i p t
    exact IsAffine.of_isIso ((Scheme.Etale.forget X ⋙ Over.forget X).map (e i p t).hom)
  have hSa (p : ℕ) (t : Fin (p + 1) → Fin m) :
      IsAffine (D.obj (S.W p t)).left := by
    have : ∀ i, IsAffine (((presentedNerve V' Q p t ⋙ Scheme.toProEt X) ⋙
        Scheme.ProEt.forget X ⋙ Over.forget X).obj i) := fun i ↦ E.affine i p t
    have : IsAffine ((Scheme.ProEt.forget X ⋙ Over.forget X).obj
        (Presheaf.cechNerveObj V' t).left) := Scheme.isAffine_of_isLimit _ (hE p t)
    exact IsAffine.of_isIso ((Scheme.ProEt.forget X ⋙ Over.forget X).map (e₀ p t).hom)
  have hπindex (i : I) {p q : ℕ} (t : Fin (p + 1) → Fin m)
      (α : Fin (q + 1) → Fin (p + 1)) :
      (mapCech S D).indexMap t α ≫ ((e₀ q (t ∘ α)).hom ≫ E.π q (t ∘ α) i ≫
          (Scheme.toProEt X).map (e i q (t ∘ α)).inv) =
        ((e₀ p t).hom ≫ E.π p t i ≫ (Scheme.toProEt X).map (e i p t).inv) ≫
          (Scheme.toProEt X).map ((R i).indexMap t α) := by
    dsimp only [e₀, e]
    rw [← Category.assoc, orderedIso_index]
    simp only [Category.assoc]
    have hw := E.π_face i q p t α
    dsimp only [V'] at hw
    rw [← Category.assoc (Presheaf.cechNerveMap (fun a ↦ Over.mk (D.map (f a))) t α).left,
      hw]
    simp only [Category.assoc, ← Functor.map_comp, orderedIso_inv_index]
  let P : CoefficientAffineCechPresentation X S J :=
    { base i := T.obj (E.W (L.obj i))
      family i a := T.obj (E.T (L.obj i) a)
      arrow i a := T.map (E.f (L.obj i) a)
      covering i := by
        have h := (CoverPreserving.of_isContinuous T X.smallEtaleTopology
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)).cover_preserve
            (E.covering (L.obj i))
        rw [Sieve.functorPushforward_ofArrows] at h
        exact h
      stage i := mapCech (R (L.obj i)) T
      trans a p t := T.map ((e _ p t).hom ≫ E.trans (L.map a) p t ≫ (e _ p t).inv)
      trans_id i p t := by
        simp only [L.map_id, E.trans_id, Category.id_comp, Iso.hom_inv_id, T.map_id]
        rfl
      trans_comp a b p t := by
        rw [← T.map_comp]
        congr 1
        simp only [L.map_comp, E.trans_comp, Category.assoc, Iso.inv_hom_id_assoc]
      trans_index := by
        intro i j a p q t α
        change T.map (_ ≫ _ ≫ _) ≫ T.map ((R _).indexMap t α) =
          T.map ((R _).indexMap t α) ≫ T.map (_ ≫ _ ≫ _)
        rw [← T.map_comp, ← T.map_comp]
        congr 1
        dsimp only [e]
        rw [Category.assoc, Category.assoc, orderedIso_inv_index,
          ← Category.assoc (E.trans _ _ _), E.trans_face]
        simp only [← Category.assoc]
        rw [← orderedIso_index]
      projection p t i := B.map
        ((e₀ p t).hom ≫ E.π p t (L.obj i) ≫
          (Scheme.toProEt X).map (e (L.obj i) p t).inv)
      projection_trans a p t := by
        change B.map (_ ≫ _ ≫ _) ≫
          B.map ((Scheme.toProEt X).map (_ ≫ _ ≫ _)) = _
        rw [← Functor.map_comp]
        congr 1
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
        rw [Functor.map_comp, ← Category.assoc (E.π p t (L.obj _)), E.π_naturality]
      projection_index := by
        intro i p q t α
        change S.indexMap t α ≫ B.map (_ ≫ _ ≫ _) =
          B.map (_ ≫ _ ≫ _) ≫
            B.map ((Scheme.toProEt X).map ((R _).indexMap t α))
        have hs : S.indexMap t α = B.map (D.map (S.indexMap t α)) := rfl
        rw [hs, ← Functor.map_comp, ← Functor.map_comp]
        congr 1
        exact hπindex (L.obj i) t α
      affine_stage i p t := hRa (L.obj i) p t
      affine_vertex := hSa }
  refine ⟨J, inferInstance, inferInstance, P, ?_⟩
  intro p t
  let N : J ⥤ X.Etale := P.nerve p t ⋙ AsSmall.down
  let en : N ≅ L ⋙ E.nerve p t := NatIso.ofComponents
    (fun i ↦ e (L.obj i) p t) (by
      intro i j a
      change (_ ≫ _ ≫ _) ≫ _ = _ ≫ _
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl)
  let H := Scheme.toProEt X ⋙ Scheme.ProEt.forget X
  let ef := Functor.isoWhiskerRight en H
  have he : IsLimit (((Scheme.ProEt.forget X).mapCone (E.nerveCone p t)).whisker L) :=
    (Functor.Initial.isLimitWhiskerEquiv L _).symm
      (isLimitOfReflects (Over.forget X) (hE p t))
  have hn := (IsLimit.postcomposeHomEquiv ef.symm _).symm he
  refine ⟨hn.ofIsoLimit (Cone.ext ((Scheme.ProEt.forget X).mapIso (e₀ p t)).symm ?_)⟩
  intro i
  symm
  change (Scheme.ProEt.forget X).map (e₀ p t).inv ≫
      (Scheme.ProEt.forget X).map
        ((e₀ p t).hom ≫ E.π p t (L.obj i) ≫
          (Scheme.toProEt X).map (e (L.obj i) p t).inv) = _
  simp only [← Functor.map_comp, Iso.inv_hom_id_assoc]
  rfl

end AlgebraicGeometry.ProEtale
