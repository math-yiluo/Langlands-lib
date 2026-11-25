/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import all WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition

/-! # Local freeness of finite etale pushforwards and unit quotients -/

@[expose] public section

universe u v
open CategoryTheory Limits Opposite Preadditive
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem finiteCommonCover
    {X : Scheme.{u}} {I : Type v} [Finite I]
    (D : I → Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ s : C.I₀, ∀ i, ∃ j, ∃ f : C.X s ⟶ (D i).X j,
        f ≫ (D i).f j = C.f s := by
  classical
  let _ := Fintype.ofFinite I
  suffices h : ∀ t : Finset I, ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ s : C.I₀, ∀ i ∈ t, ∃ j, ∃ f : C.X s ⟶ (D i).X j,
        f ≫ (D i).f j = C.f s by
    obtain ⟨C, hC⟩ := h Finset.univ
    exact ⟨C, fun s i ↦ hC s i (Finset.mem_univ i)⟩
  intro t
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨X.affineCover.weaken Scheme.zariskiPrecoverage_le_proetalePrecoverage,
      fun _ _ h ↦ False.elim (Finset.notMem_empty _ h)⟩
  | @insert i t hi ih =>
    obtain ⟨C, hC⟩ := ih
    let C' := C.bind (fun s ↦ (D i).pullback₁ (C.f s))
    refine ⟨C', ?_⟩
    rintro ⟨s, j⟩ k hk
    by_cases hki : k = i
    · subst k
      exact ⟨j, pullback.snd _ _, pullback.condition.symm⟩
    · obtain ⟨l, f, hf⟩ := hC s k ((Finset.mem_insert.mp hk).resolve_left hki)
      exact ⟨l, pullback.fst _ _ ≫ f, by
        rw [Category.assoc, hf]; rfl⟩

private theorem finiteProduct_free
    {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {I : Type v} [Finite I]
    (M : I → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : ∀ i, Mod.IsFree R (M i)) : Mod.IsFree R (∏ᶜ M) := by
  classical
  let _ := Fintype.ofFinite I
  choose n hn using hM
  let e := fun i ↦ (hn i).some
  let J := Σ i, Fin (n i)
  exact ⟨Fintype.card J, ⟨(biproduct.isoProduct M).symm ≪≫
    biproduct.mapIso e ≪≫
    biproductBiproductIso (fun i ↦ Fin (n i)) (fun _ _ ↦ Mod.regular R) ≪≫
    biproduct.whiskerEquiv (f := fun _ : J ↦ Mod.regular R)
      (g := fun _ : Fin (Fintype.card J) ↦ Mod.regular R)
      (Fintype.equivFin J) (fun _ ↦ Iso.refl _)⟩⟩

private theorem free_standard_refine
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (g : Y ⟶ X) (f : Z ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : Mod.IsFree (condensedRingObj Λ Y) ((upperStar Λ g).obj M)) :
    Mod.IsFree (condensedRingObj Λ Z) ((upperStar Λ (f ≫ g)).obj M) := by
  obtain ⟨n, ⟨e⟩⟩ := IsFree.upperStar Λ f h
  exact ⟨n, ⟨(upperStarComp Λ f g).app M ≪≫ e⟩⟩

-- Keep the member property abstract while reducing the pullback-cover construction.
private theorem exists_cover_pullback_property
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (Q : ∀ Z : Scheme.{u}, (Z ⟶ Y) → Prop)
    (hQ : ∀ s : C.I₀, Q (pullback f (C.f s)) (pullback.fst f (C.f s))) :
    ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage Y,
      ∀ s : D.I₀, Q (D.X s) (D.f s) :=
  ⟨C.pullback₁ f, hQ⟩


private theorem locFree_product
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {I : Type v} [Finite I]
    (M : I → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∀ i, IsLocallyFree (condensedRingObj Λ X) (M i)) :
    IsLocallyFree (condensedRingObj Λ X) (∏ᶜ M) := by
  classical
  obtain ⟨D, hD⟩ := Classical.skolem.mp fun i ↦ (isLocallyFree_iff (M i)).1 (hM i)
  obtain ⟨C, hC⟩ := finiteCommonCover D
  refine (isLocallyFree_iff _).2 ⟨C, ?_⟩
  intro s
  let H := upperStar Λ (C.f s)
  have h (i : I) : Mod.IsFree (condensedRingObj Λ (C.X s)) (H.obj (M i)) := by
    obtain ⟨j, f, hf⟩ := hC s i
    have hh := free_standard_refine Λ ((D i).f j) f (M i) (hD i j)
    rwa [hf] at hh
  exact free_of_iso (finiteProduct_free (fun i ↦ H.obj (M i)) h)
    (PreservesProduct.iso H M).symm

private theorem locFree_of_cover
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ s, IsLocallyFree (condensedRingObj Λ (C.X s)) ((upperStar Λ (C.f s)).obj M)) :
    IsLocallyFree (condensedRingObj Λ X) M := by
  apply (isLocallyFree_iff M).2
  apply exists_cover_of_local_property C
    (fun Y f ↦ Mod.IsFree (condensedRingObj Λ Y) ((upperStar Λ f).obj M))
  intro s
  obtain ⟨D, hD⟩ := (isLocallyFree_iff _).1 (h s)
  refine ⟨D, fun t ↦ ?_⟩
  exact free_of_iso (hD t) ((upperStarComp Λ (D.f t) (C.f s)).app M).symm

-- Check cover projections with an abstract predicate, before substituting module objects.
private theorem exists_etale_cover_with_property
    {X : Scheme.{u}} (Y : X → Scheme.{u}) (g : ∀ x, Y x ⟶ X) (y : ∀ x, Y x)
    (hg : ∀ x, Etale (g x)) (hy : ∀ x, g x (y x) = x)
    (Q : ∀ Z : Scheme.{u}, (Z ⟶ X) → Prop) (hQ : ∀ x, Q (Y x) (g x)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X,
      ∀ s : C.I₀, Q (C.X s) (C.f s) := by
  let D : Scheme.Cover.{u} (Scheme.precoverage @Etale) X :=
    Scheme.Cover.mkOfCovers X Y g (fun x ↦ ⟨x, y x, hy x⟩) hg
  exact ⟨D.weaken Scheme.etalePrecoverage_le_proetalePrecoverage, hQ⟩

private theorem diagonal_cokernel
    {C : Type*} [Category* C] [Abelian C] [HasFiniteBiproducts C] {J : Type u} [Finite J]
    (A : C) (j₀ : J) :
    Nonempty (cokernel (biproduct.lift (fun _ : J ↦ 𝟙 A)) ≅
      ⨁ (fun _ : {j : J // j ≠ j₀} ↦ A)) := by
  classical
  let D : C := ⨁ (fun _ : J ↦ A)
  let δ : A ⟶ D := biproduct.lift (fun _ ↦ 𝟙 A)
  let d : D ≅ D :=
    { hom := biproduct.lift (fun j ↦ if j = j₀ then biproduct.π (fun _ : J ↦ A) j
        else biproduct.π (fun _ : J ↦ A) j - biproduct.π (fun _ : J ↦ A) j₀)
      inv := biproduct.lift (fun j ↦ if j = j₀ then biproduct.π (fun _ : J ↦ A) j
        else biproduct.π (fun _ : J ↦ A) j + biproduct.π (fun _ : J ↦ A) j₀)
      hom_inv_id := by
        apply biproduct.hom_ext
        intro j
        by_cases hj : j = j₀ <;> simp [hj, Category.assoc, comp_add]
      inv_hom_id := by
        apply biproduct.hom_ext
        intro j
        by_cases hj : j = j₀ <;> simp [hj, Category.assoc, comp_sub] }
  have hd : δ ≫ d.hom = biproduct.ι (fun _ : J ↦ A) j₀ := by
    apply biproduct.hom_ext
    intro j
    by_cases hj : j = j₀
    · subst j
      simp [δ, d]
    · simp [δ, d, hj, biproduct.ι_π_ne _ (Ne.symm hj), comp_sub]
  exact ⟨cokernel.mapIso _ _ (Iso.refl A) d (by simpa using hd) ≪≫
    cokernelBiproductιIso (fun _ : J ↦ A) j₀⟩

private theorem exists_split_sections
    {X U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p] (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (y : Y), Etale g ∧ g y = x ∧
      ∃ (n : ℕ) (_ : 0 < n) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g),
        Nonempty (IsColimit (Cofan.mk (pullback p g)
          (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))) := by
  classical
  obtain ⟨Y, g, y, hg, hy, J, V, ι, hJ, ⟨hc⟩, hi, he⟩ :=
    finite_etale_etale_local_split p x
  let _ := hg
  let _ := hJ
  let _ := Fintype.ofFinite J
  choose e he using he
  have hne : Nonempty J := by
    obtain ⟨z, hz⟩ := (pullback.snd p g).surjective y
    let a : (∐ V) ≅ pullback p g := colimit.isoColimitCocone ⟨Cofan.mk _ ι, hc⟩
    obtain ⟨j, z', hj⟩ := (sigmaOpenCover V).exists_eq (a.inv z)
    exact ⟨j⟩
  let _ := hne
  let n := Fintype.card J
  let q : Fin n ≃ J := (Fintype.equivFin J).symm
  let b (k : Fin n) : Y ⟶ pullback p g := (e (q k)).inv ≫ ι (q k)
  have hb (k : Fin n) : b k ≫ pullback.snd p g = 𝟙 Y := by
    dsimp [b]
    rw [Category.assoc, ← he, Iso.inv_hom_id]
  let t (k : Fin n) := b k ≫ pullback.fst p g
  have w (k : Fin n) : t k ≫ p = g := by
    dsimp [t]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hb, Category.id_comp]
  have hlift (k : Fin n) :
      pullback.lift (t k) (𝟙 Y) (by simpa using w k) = b k := by
    apply pullback.hom_ext <;> simp [t, hb]
  have hbcol : IsColimit (Cofan.mk (pullback p g) b) := by
    let K (c : Cofan (fun _ : Fin n ↦ Y)) : Cofan V :=
      Cofan.mk c.pt (fun j ↦ (e j).hom ≫ c.inj (q.symm j))
    refine Cofan.IsColimit.mk _ (fun c ↦ hc.desc (K c)) ?_ ?_
    · intro c k
      dsimp [b]
      have hf := hc.fac (K c) ⟨q k⟩
      change ι (q k) ≫ hc.desc (K c) = (e (q k)).hom ≫ c.inj _ at hf
      rw [Category.assoc, hf]
      simp
    · intro c m hm
      apply hc.hom_ext
      rintro ⟨j⟩
      change ι j ≫ m = ι j ≫ hc.desc (K c)
      have hf := hc.fac (K c) ⟨j⟩
      change ι j ≫ hc.desc (K c) = (e j).hom ≫ c.inj (q.symm j) at hf
      rw [hf]
      have h := hm (q.symm j)
      change ((e (q (q.symm j))).inv ≫ ι (q (q.symm j))) ≫ m = _ at h
      rw [q.apply_symm_apply] at h
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
        congrArg (fun z ↦ (e j).hom ≫ z) h
  refine ⟨Y, g, y, hg, hy, n, Fintype.card_pos, t, w, ?_⟩
  simpa only [hlift] using (show Nonempty (IsColimit (Cofan.mk _ b)) from ⟨hbcol⟩)

private theorem sheetUnit
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
    {H : C ⥤ E} {K : D ⥤ E} (a : H ≅ F ⋙ K) (P : C) :
    H.map (adj.unit.app P) ≫ a.hom.app (R.obj (F.obj P)) ≫
      K.map (adj.counit.app (F.obj P)) = a.hom.app P := by
  have h := a.hom.naturality (adj.unit.app P)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h
  rw [← Category.assoc, h, Category.assoc, ← K.map_comp,
    adj.left_triangle_components, K.map_id, Category.comp_id]

private theorem localProductComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    {Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j))))) :
      ∃ ε : ∀ N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj Λ U),
        (upperStar Λ g).obj ((lowerStar Λ p).obj N) ≅
          ∏ᶜ (fun j ↦ (upperStar Λ (t j)).obj N),
      ∀ (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) (j : Fin n),
        (upperStar Λ g).map ((upperStarLowerStarAdjunction Λ p).unit.app P) ≫
          (ε ((upperStar Λ p).obj P)).hom ≫
            Pi.π (fun j ↦ (upperStar Λ (t j)).obj ((upperStar Λ p).obj P)) j =
        ((eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
          upperStarComp Λ (t j) p).hom.app P := by
  classical
  let a (j : Fin n) : upperStar Λ g ≅ upperStar Λ p ⋙ upperStar Λ (t j) :=
    (eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫ upperStarComp Λ (t j) p
  let q (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)) :
      (upperStar Λ g).obj ((lowerStar Λ p).obj N) ⟶
        ∏ᶜ (fun j ↦ (upperStar Λ (t j)).obj N) := Pi.lift (fun j ↦
    (a j).hom.app ((lowerStar Λ p).obj N) ≫
      (upperStar Λ (t j)).map ((upperStarLowerStarAdjunction Λ p).counit.app N))
  have hq (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)) : IsIso (q N) :=
    splitProEtaleModuleProductMap_isIso Λ p g n t w hc N
  let ε (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj Λ U)) :
      (upperStar Λ g).obj ((lowerStar Λ p).obj N) ≅
        ∏ᶜ (fun j ↦ (upperStar Λ (t j)).obj N) := by
    let _ := hq N
    exact asIso (q N)
  refine ⟨ε, ?_⟩
  intro P j
  dsimp only [ε, asIso_hom]
  simp only [q, Pi.lift_comp_π]
  exact sheetUnit (upperStarLowerStarAdjunction Λ p) (a j) P

private theorem locFree_push_of_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X)
    (n : ℕ) (t : Fin n → (Y ⟶ U))
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (ε : (upperStar Λ g).obj ((lowerStar Λ p).obj M) ≅
      ∏ᶜ (fun j ↦ (upperStar Λ (t j)).obj M))
    (hM : IsLocallyFree (condensedRingObj Λ U) M) :
    IsLocallyFree (condensedRingObj Λ Y) ((upperStar Λ g).obj ((lowerStar Λ p).obj M)) := by
  exact IsLocallyFree.of_iso ε.symm (locFree_product Λ _
    (fun j ↦ hM.upperStar Λ (t j)))

private theorem locFree_unitCokernel_of_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X) (g : Y ⟶ X)
    (n : ℕ) (hn : 0 < n) (t : Fin n → (Y ⟶ U))
    (a₀ : ∀ j, upperStar Λ g ≅ upperStar Λ p ⋙ upperStar Λ (t j))
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (ε : (upperStar Λ g).obj ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ≅
      ∏ᶜ (fun j ↦ (upperStar Λ (t j)).obj ((upperStar Λ p).obj P)))
    (hε : ∀ j, (upperStar Λ g).map ((upperStarLowerStarAdjunction Λ p).unit.app P) ≫
      ε.hom ≫ Pi.π (fun j ↦ (upperStar Λ (t j)).obj ((upperStar Λ p).obj P)) j =
        (a₀ j).hom.app P)
    (hP : IsLocallyFree (condensedRingObj Λ X) P) :
    IsLocallyFree (condensedRingObj Λ Y) ((upperStar Λ g).obj
      (cokernel ((upperStarLowerStarAdjunction Λ p).unit.app P))) := by
  classical
  let H := upperStar Λ g
  let A := H.obj P
  let η := (upperStarLowerStarAdjunction Λ p).unit.app P
  let a (j : Fin n) : A ≅ (upperStar Λ (t j)).obj ((upperStar Λ p).obj P) :=
    (a₀ j).app P
  let b : H.obj ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ≅
      ⨁ (fun _ : Fin n ↦ A) :=
    ε ≪≫ Pi.mapIso (fun j ↦ (a j).symm) ≪≫
      (biproduct.isoProduct (fun _ : Fin n ↦ A)).symm
  have hδ : H.map η ≫ b.hom = biproduct.lift (fun _ : Fin n ↦ 𝟙 A) := by
    apply biproduct.hom_ext
    intro j
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      biproduct.isoProduct_inv, biproduct.lift_π, Pi.mapIso_hom_π, Category.assoc]
    have hu : H.map η ≫ (ε).hom ≫
        Pi.π (fun j ↦ (upperStar Λ (t j)).obj ((upperStar Λ p).obj P)) j =
          (a j).hom := hε j
    simpa only [Category.assoc] using
      (congrArg (fun z ↦ z ≫ (a j).inv) hu).trans (a j).hom_inv_id
  let j₀ : Fin n := ⟨0, hn⟩
  obtain ⟨d⟩ := diagonal_cokernel A j₀
  let e := PreservesCokernel.iso H η ≪≫
    cokernel.mapIso _ _ (Iso.refl A) b
      (hδ.trans (Category.id_comp _).symm) ≪≫ d ≪≫
      biproduct.isoProduct (fun _ : {j : Fin n // j ≠ j₀} ↦ A)
  exact IsLocallyFree.of_iso e.symm (locFree_product Λ _
    (fun _ ↦ hP.upperStar Λ g))

/-- Finite etale pushforward and the quotient by its unit preserve local finite freeness.

Source: Stacks Project, Tag 095B, its split finite-cover computation, and
Bhatt--Scholze, Section 6.8, finite etale descent of lisse coefficients.
(auxiliary; not a blueprint node)

Proof in words. Around every point split the finite etale map over an etale
neighbourhood. Surjectivity makes the finite sheet set nonempty. Reindex it by
Fin n and assemble these neighbourhoods into an etale, hence pro-etale, cover.
The canonical sheet product map identifies the restriction of a pushforward
with the product of the sheet restrictions. Pull back the supplied free covers
to the sheets and take their finite common refinement. Finite products of finite
free modules are finite free, by flattening their biproduct index sets. Bind the
resulting covers to the splitting cover to prove the pushforward assertion.
For the unit, the triangle identity and naturality of inverse-image comparison
identify its components with identities of the pulled-back source. Choose one
sheet. The automorphism which subtracts that coordinate from all other
coordinates takes the diagonal to the chosen biproduct injection. Its cokernel
is the sum over the remaining sheets, hence is locally finite free. Exactness of
inverse image commutes with this cokernel. Finally transport freeness between
the raw pulled coefficient ring and the standard coefficient ring along the
canonical coefficient isomorphism. Empty bases and one-sheet covers are included.
-/
theorem finiteEtale_locallyFree_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] [Surjective p] :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U),
      (IsLocallyFree (condensedRingObj Λ U) M) →
      IsLocallyFree (condensedRingObj Λ X) ((lowerStar Λ p).obj M)) ∧
    (∀ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      (IsLocallyFree (condensedRingObj Λ X) P) →
      IsLocallyFree (condensedRingObj Λ X)
        (cokernel ((upperStarLowerStarAdjunction Λ p).unit.app P))) := by
  classical
  obtain ⟨Y, hY⟩ := Classical.skolem.mp (exists_split_sections p)
  obtain ⟨g, hg'⟩ := Classical.skolem.mp hY
  obtain ⟨y, hy'⟩ := Classical.skolem.mp hg'
  have hg := fun x ↦ (hy' x).1
  have hy := fun x ↦ (hy' x).2.1
  obtain ⟨n, hn'⟩ := Classical.skolem.mp (fun x ↦ (hy' x).2.2)
  obtain ⟨hn, ht'⟩ := Classical.skolem.mp hn'
  obtain ⟨t, hw'⟩ := Classical.skolem.mp ht'
  obtain ⟨w, hc⟩ := Classical.skolem.mp hw'
  constructor
  · intro M hM
    have hB : IsLocallyFree (condensedRingObj Λ X) ((lowerStar Λ p).obj M) := by
      obtain ⟨C, hC⟩ := exists_etale_cover_with_property Y g y hg hy
        (fun Z f ↦ IsLocallyFree (condensedRingObj Λ Z)
          ((upperStar Λ f).obj ((lowerStar Λ p).obj M))) (by
          intro x
          have : Etale (g x) := hg x
          obtain ⟨ε, hε⟩ := localProductComparison Λ p (g x) (n x) (t x) (w x) (hc x)
          exact locFree_push_of_comparison Λ p (g x) (n x) (t x) M (ε M) hM)
      exact locFree_of_cover _ C hC
    exact hB
  · intro P hP
    have hQ : IsLocallyFree (condensedRingObj Λ X)
        (cokernel ((upperStarLowerStarAdjunction Λ p).unit.app P)) := by
      obtain ⟨C, hC⟩ := exists_etale_cover_with_property Y g y hg hy
        (fun Z f ↦ IsLocallyFree (condensedRingObj Λ Z) ((upperStar Λ f).obj
          (cokernel ((upperStarLowerStarAdjunction Λ p).unit.app P)))) (by
          intro x
          have : Etale (g x) := hg x
          obtain ⟨ε, hε⟩ := localProductComparison Λ p (g x) (n x) (t x) (w x) (hc x)
          exact locFree_unitCokernel_of_comparison Λ p (g x) (n x) (hn x) (t x)
            (fun j ↦ (eqToIso (congrArg (upperStar Λ) (w x j))).symm ≪≫
              upperStarComp Λ (t x j) p) P (ε ((upperStar Λ p).obj P)) (hε P) hP)
      exact locFree_of_cover _ C hC
    exact hQ

end AlgebraicGeometry.ProEtale.CondensedRing
