/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible

/-! # Local lifting along represented epimorphisms on the pro-etale site
Source: Stacks Project, Tags 00WN, 098I and 0990.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

-- Transport an objectwise small large-valued sheaf to the original value universe.
open CategoryTheory.Limits CategoryTheory.Functor in
private noncomputable def shrinkIso {C : Type (u + 1)} [Category.{u} C]
    (P : C ⥤ Type (u + 1)) [FunctorToTypes.Small.{u} P] :
    FunctorToTypes.shrink.{u} P ⋙ uliftFunctor.{u + 1, u} ≅ P :=
  NatIso.ofComponents
    (fun U ↦ (Equiv.ulift.trans (equivShrink (P.obj U)).symm).toIso)
    (by
      intro U V f
      ext x
      change (equivShrink _).symm ((equivShrink _) _) = _
      exact (equivShrink _).symm_apply_apply _)

open CategoryTheory.Limits CategoryTheory.Functor in
private noncomputable def shrinkSheaf {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (F : Sheaf J (Type (u + 1)))
    [FunctorToTypes.Small.{u} F.obj] : Sheaf J (Type u) where
  obj := FunctorToTypes.shrink.{u} F.obj
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp J _ uliftFunctor.{u + 1, u}
    exact (Presheaf.isSheaf_of_iso_iff (shrinkIso F.obj)).mpr F.property

open CategoryTheory.Limits CategoryTheory.Functor in
private noncomputable def shrinkSheafIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (F : Sheaf J (Type (u + 1)))
    [FunctorToTypes.Small.{u} F.obj] :
    (sheafCompose J uliftFunctor.{u + 1, u}).obj (shrinkSheaf J F) ≅ F where
  hom := ⟨(shrinkIso F.obj).hom⟩
  inv := ⟨(shrinkIso F.obj).inv⟩
  hom_inv_id := by ext1; exact (shrinkIso F.obj).hom_inv_id
  inv_hom_id := by ext1; exact (shrinkIso F.obj).inv_hom_id

open CategoryTheory.Limits CategoryTheory.Functor in
private noncomputable def shrunkSheafification {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    (hsmall : ∀ P : Cᵒᵖ ⥤ Type u,
      FunctorToTypes.Small.{u} (sheafify J (P ⋙ uliftFunctor.{u + 1, u}))) :
    (Cᵒᵖ ⥤ Type u) ⥤ Sheaf J (Type u) where
  obj P := by
    letI := hsmall P
    exact shrinkSheaf J ((presheafToSheaf J _).obj (P ⋙ uliftFunctor.{u + 1, u}))
  map {P Q} f := by
    letI := hsmall P
    letI := hsmall Q
    exact ⟨FunctorToTypes.shrinkMap
      ((presheafToSheaf J _).map (whiskerRight f uliftFunctor.{u + 1, u})).hom⟩
  map_id P := by
    ext U x
    simp [FunctorToTypes.shrinkMap]
  map_comp f g := by
    ext U x
    simp [FunctorToTypes.shrinkMap]

open CategoryTheory.Limits CategoryTheory.Functor in
private noncomputable def shrunkSheafificationIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    (hsmall : ∀ P : Cᵒᵖ ⥤ Type u,
      FunctorToTypes.Small.{u} (sheafify J (P ⋙ uliftFunctor.{u + 1, u}))) :
    (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{u + 1, u} ⋙
      presheafToSheaf J (Type (u + 1)) ≅
    shrunkSheafification J hsmall ⋙ sheafCompose J uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents (fun P ↦ by
    letI := hsmall P
    exact (shrinkSheafIso J ((presheafToSheaf J _).obj
      (P ⋙ uliftFunctor.{u + 1, u}))).symm)
    (by
      intro P Q f
      ext U x
      simp [shrunkSheafification, shrinkSheafIso, shrinkIso, FunctorToTypes.shrinkMap, Equiv.ulift])

-- Restrict the large sheafification adjunction along the fully faithful universe lifts.
-- Its left exactness descends because the lift reflects finite limits.
open CategoryTheory.Limits CategoryTheory.Functor in
private theorem hasSmallSheafify {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    (hsmall : ∀ P : Cᵒᵖ ⥤ Type u,
      FunctorToTypes.Small.{u} (sheafify J (P ⋙ uliftFunctor.{u + 1, u}))) :
    HasSheafify J (Type u) := by
  let L := shrunkSheafification J hsmall
  let iC := (Functor.whiskeringRight Cᵒᵖ _ _).obj uliftFunctor.{u + 1, u}
  let iD := sheafCompose J uliftFunctor.{u + 1, u}
  let e : iC ⋙ presheafToSheaf J (Type (u + 1)) ≅ L ⋙ iD := shrunkSheafificationIso J hsmall
  have : PreservesFiniteLimits iC := by
    constructor
    intro K _ _
    dsimp [iC]
    infer_instance
  have : PreservesFiniteLimits (iC ⋙ presheafToSheaf J (Type (u + 1))) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (L ⋙ iD) := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteLimits L := preservesFiniteLimits_of_reflects_of_preserves L iD
  exact HasSheafify.mk' J (Type u)
    ((sheafificationAdjunction J (Type (u + 1))).restrictFullyFaithful
      (iC := iC) (iD := iD) (L := L) (R := sheafToPresheaf J (Type u))
      (fullyFaithfulULiftFunctor.{u + 1, u}.whiskeringRight Cᵒᵖ)
      (fullyFaithfulSheafCompose J fullyFaithfulULiftFunctor.{u + 1, u}) e (Iso.refl _))

namespace AlgebraicGeometry.Scheme.ProEt

open CategoryTheory.Limits CategoryTheory.Functor in
private def HasOpenRefinements {X : Scheme.{u}} (W : X.ProEt) : Prop :=
  ∀ S ∈ topology X W, ∃ (ι : Type u) (O : ι → W.left.Opens),
    (∀ i, S (ofOpenImmersionHom W (O i).ι)) ∧
      Sieve.ofArrows (fun i ↦ ofOpenImmersion W (O i).ι)
        (fun i ↦ ofOpenImmersionHom W (O i).ι) ∈ topology X W

-- Encode a section by the set of all its representatives on opens. This lives in Type u,
-- even when the section does not. A covering open refinement makes the encoding injective.
open CategoryTheory.Limits CategoryTheory.Functor in
private theorem small_sections_of_open_refinements {X : Scheme.{u}} (W : X.ProEt)
    (hW : HasOpenRefinements W) (P : X.ProEtᵒᵖ ⥤ Type u)
    (G : Sheaf (topology X) (Type (u + 1)))
    (η : P ⋙ uliftFunctor.{u + 1, u} ⟶ G.obj)
    [Presheaf.IsLocallySurjective (topology X) η] :
    Small.{u} (G.obj.obj (op W)) := by
  let code (s : G.obj.obj (op W)) :
      Set (Σ O : W.left.Opens, P.obj (op (ofOpenImmersion W O.ι))) :=
    {p | η.app _ ⟨p.2⟩ = G.obj.map (ofOpenImmersionHom W p.1.ι).op s}
  apply small_of_injective (f := code)
  intro s t h
  obtain ⟨ι, O, hO, hcov⟩ := hW _ (Presheaf.imageSieve_mem (topology X) η s)
  refine Sheaf.isSeparated G W _ hcov s t ?_
  rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
  obtain ⟨p, hp⟩ := hO i
  have hc : (⟨O i, p.down⟩ : Σ O : W.left.Opens,
      P.obj (op (ofOpenImmersion W O.ι))) ∈ code s := hp
  rw [h] at hc
  have he : G.obj.map (ofOpenImmersionHom W (O i).ι).op s =
      G.obj.map (ofOpenImmersionHom W (O i).ι).op t := hp.symm.trans hc
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using congrArg (G.obj.map a.op) he

open CategoryTheory.Limits CategoryTheory.Functor in
private theorem open_refinement_of_split_cover {X : Scheme.{u}} {W : X.ProEt}
    {κ : Type u} {V : κ → Scheme.{u}} (v : ∀ j, V j ⟶ W.left)
    (s : W.left ⟶ ∐ V) (hs : s ≫ Sigma.desc v = 𝟙 _) (S : Sieve W)
    (hS : ∀ j {Y : X.ProEt} (a : Y ⟶ W) (b : Y.left ⟶ V j), b ≫ v j = a.left → S a) :
    ∃ (O : κ → W.left.Opens),
      (∀ i, S (ofOpenImmersionHom W (O i).ι)) ∧
        Sieve.ofArrows (fun i ↦ ofOpenImmersion W (O i).ι)
          (fun i ↦ ofOpenImmersionHom W (O i).ι) ∈ topology X W := by
  let O (j : κ) : W.left.Opens := s ⁻¹ᵁ (Sigma.ι V j).opensRange
  have hO (j : κ) : Set.range ((O j).ι ≫ s).base ⊆ Set.range (Sigma.ι V j).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨O, fun j ↦ hS j _ (IsOpenImmersion.lift (Sigma.ι V j) ((O j).ι ≫ s) (hO j))
    ?_, ?_⟩
  · rw [← Sigma.ι_comp_desc v j, ← Category.assoc, IsOpenImmersion.lift_fac,
      Category.assoc, hs, Category.comp_id]
    rfl
  · refine mem_topology_of_openImmersion _ (fun j ↦ (O j).ι) (fun x ↦ ?_)
      (fun j ↦ Sieve.ofArrows_mk _ _ j)
    obtain ⟨j, y, hy⟩ := (sigmaOpenCover V).exists_eq (s x)
    refine ⟨j, ?_⟩
    rw [Opens.range_ι]
    exact ⟨y, hy⟩

-- The geometric argument of isWeaklyContractible_of_iso, retaining the open refinements
-- needed for the size estimate instead of just their abstract weak contractibility.
open CategoryTheory.Limits CategoryTheory.Functor in
private theorem open_refinements_of_isWContractible {X : Scheme.{u}} {W : X.ProEt}
    {R : CommRingCat.{u}} [IsWContractibleRing R] (e : W.left ≅ Spec R) :
    HasOpenRefinements W := by
  intro S hS
  obtain ⟨P, hP, hPS⟩ := mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (mem_precoverage_iff.1 hP)
  have : IsAffine W.left := .of_isIso e.hom
  obtain ⟨𝒱, g, _, _⟩ := Cover.QuasiCompact.exists_hom.{u + 1, u} 𝒰
  have hmem (i : 𝒰.I₀) : P.map (ProEt.forget X ⋙ Over.forget X) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  let ε : ULift.{u} (Fin (Nat.card 𝒱.I₀)) ≃ 𝒱.I₀ :=
    Equiv.ulift.trans (Finite.equivFin _).symm
  let v (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) := 𝒱.f (ε k)
  have : WeaklyEtale (Sigma.desc v) := IsZariskiLocalAtSource.sigmaDesc fun k ↦ 𝒱.map_prop _
  have : Surjective (Sigma.desc v) := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨k, hk⟩ := ε.surjective (𝒱.idx x)
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [v]
    rw [hk]
    exact 𝒱.covers x
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isWContractibleRing (Sigma.desc v ≫ e.hom)
  have hsplit : (e.hom ≫ s) ≫ Sigma.desc v = 𝟙 _ := by
    rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hs]
    simp
  have hfactor : ∀ j {Y : X.ProEt} (b : Y ⟶ W) (c : Y.left ⟶ Spec (𝒱.X (ε j))),
      c ≫ v j = b.left → S b := by
    intro j Y b c hbc
    have ha' (i : 𝒰.I₀) : (a i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZa i
    let d : Y.left ⟶ (Z (g.s₀ (ε j))).left := c ≫ g.h₀ (ε j) ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ (ε j))).left = b.left := by
      rw [← hbc, ha', Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, g.w₀]
      rfl
    have hb : b = MorphismProperty.Over.homMk d (by
        rw [← MorphismProperty.Over.w (a (g.s₀ (ε j))), ← Category.assoc, hd]
        exact MorphismProperty.Over.w b) ≫ a (g.s₀ (ε j)) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [hb]
    exact S.downward_closed (hPS _ _ (ha _)) _
  obtain ⟨O, hO, hcov⟩ := open_refinement_of_split_cover v (e.hom ≫ s) hsplit S hfactor
  exact ⟨_, O, hO, hcov⟩

open CategoryTheory.Limits CategoryTheory.Functor in
private theorem exists_open_refinement_cover {X : Scheme.{u}} (V : X.ProEt) :
    ∃ (ι : Type u) (W : ι → X.ProEt) (f : ∀ i, W i ⟶ V),
      (∀ i, HasOpenRefinements (W i)) ∧ Sieve.ofArrows W f ∈ topology X V := by
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let U (x : 𝒜.I₀) := ofOpenImmersion V (𝒜.f x)
  let W (x : 𝒜.I₀) : X.ProEt := ProEt.mk (Spec.map (φ x) ≫ (U x).hom)
  let w (x : 𝒜.I₀) : W x ⟶ U x := MorphismProperty.Over.homMk (Spec.map (φ x)) rfl
  refine ⟨𝒜.I₀, W, fun x ↦ w x ≫ ofOpenImmersionHom V (𝒜.f x), ?_, ?_⟩
  · intro x
    have := hw x
    exact open_refinements_of_isWContractible (R := CommRingCat.of (S x)) (Iso.refl _)
  · have hU : Sieve.ofArrows U (fun x ↦ ofOpenImmersionHom V (𝒜.f x)) ∈ topology X V :=
      mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
        (fun x ↦ Sieve.ofArrows_mk _ _ x)
    refine (topology X).transitive hU _ fun Y g hg ↦ ?_
    obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hg
    rw [Sieve.pullback_comp]
    refine (topology X).pullback_stable c ((topology X).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x)) ?_))
    · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
      rw [Sieve.pullback_apply, Category.assoc]
      exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ x) d
    · rw [mem_precoverage_iff, Presieve.map_singleton]
      exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
        inferInstance

-- On an arbitrary object, separatedness injects sections into the product of the sections
-- on a fixed small covering by the preceding spectra.
open CategoryTheory.Limits CategoryTheory.Functor in
private theorem small_sheafify (X : Scheme.{u}) (P : X.ProEtᵒᵖ ⥤ Type u) :
    FunctorToTypes.Small.{u} (sheafify (topology X) (P ⋙ uliftFunctor.{u + 1, u})) := by
  intro U
  let G := (presheafToSheaf (topology X) (Type (u + 1))).obj
    (P ⋙ uliftFunctor.{u + 1, u})
  let η := toSheafify (topology X) (P ⋙ uliftFunctor.{u + 1, u})
  obtain ⟨ι, W, f, hW, hcov⟩ := exists_open_refinement_cover U.unop
  have (i : ι) : Small.{u} (G.obj.obj (op (W i))) :=
    small_sections_of_open_refinements (W i) (hW i) P G η
  apply small_of_injective (f := fun s : G.obj.obj U ↦ fun i ↦ G.obj.map (f i).op s)
  intro s t h
  refine Sheaf.isSeparated G U.unop _ hcov s t ?_
  rintro Z g ⟨_, a, _, ⟨i⟩, rfl⟩
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using
    congrArg (G.obj.map a.op) (congrFun h i)

open CategoryTheory.Limits CategoryTheory.Functor in
private theorem proetale_hasSmallSheafify (X : Scheme.{u}) :
    HasSheafify (topology X) (Type u) :=
  hasSmallSheafify (topology X) (small_sheafify X)

/-- An epimorphism between represented sheaves lifts each represented section locally.
Source: Stacks Project, Tag 00WN, with the small pro-etale site of Tag 098K and
bounded affine weakly contractible refinements of Tags 098I and 0990.
(auxiliary; not a blueprint node).

Proof: use the image sieve of the section g under the represented map of mu.
Its membership at f:V→T is exactly the existence of t with t mu=f g. The
sheaf-epimorphism/local-surjectivity criterion says this image sieve is covering;
choose that sieve and read its membership witnesses to obtain the conclusion.

The criterion must be established in the value universe of these representables.
One can use the usual associated-sheaf construction in that universe: on an
arbitrary object first take a small affine open cover, and on each affine fix a
bounded affine weakly contractible pro-etale refinement. On a fixed such compact
projective object every covering is refined by a finite clopen partition: lift
its covering epimorphism to the sheaf coproduct, then use the clopen component
partition and compactness. The partitions of the fixed small scheme form a small
type. Matching families and their refinement colimits are therefore small there;
descent across the fixed covers constructs small associated sheaves on the
original objects. The associated-sheaf adjunction is left exact by the usual
finite-limit argument. Thus the epi/local-surjectivity criterion applies to the
Type-u-valued represented sheaves, without replacing their epi hypothesis by a
larger-universe one. Isomorphisms give the top sieve; empty sources and empty
targets are handled by the same image-sieve argument. -/
theorem representable_epi_local_lifting
    (X : Scheme.{u}) {A B : X.ProEt} (μ : A ⟶ B)
    (hμ : Epi ((topology X).yoneda.map μ)) (T : X.ProEt) (g : T ⟶ B) :
    ∃ S : Sieve T, S ∈ topology X T ∧
      ∀ (V : X.ProEt) (f : V ⟶ T), S f → ∃ t : V ⟶ A, t ≫ μ = f ≫ g := by
  let := proetale_hasSmallSheafify X
  have := (Sheaf.isLocallySurjective_iff_epi ((topology X).yoneda.map μ)).mpr hμ
  exact ⟨Presheaf.imageSieve ((topology X).yoneda.map μ).hom g,
    Presheaf.imageSieve_mem (topology X) ((topology X).yoneda.map μ).hom g,
    fun V f hf ↦ hf⟩

end AlgebraicGeometry.Scheme.ProEt
