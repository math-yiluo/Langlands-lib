/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleModuleStalkSpecialization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFiniteStalkLocalPresentation
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSectionGermSpecialization
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSectionGermNoetherianNeighborhood
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSectionGermIsoSupplement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Finite stalks and specialization imply finite local constancy

Source: Stacks Project, Tag 0GKC, lemma-characterize-locally-constant-module, (2) implies (1)
(blueprint: lem-weil-pbc-etale-finite-stalk-specialization-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem sectionGerm_bijective_normalize
    {S : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : S.Etale) (M : ModuleCat.{u + 1} Λ) (f : M ⟶ G.obj.obj (Opposite.op U))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (b : Spec (.of Ω) ⟶ U.left) (hb : b ≫ U.hom = s) :
    Function.Bijective
      (f ≫ (pointSmallEtale s).toPresheafFiber U (Over.homMk b hb) G.obj) ↔
    Function.Bijective (f ≫ (pointSmallEtale (b ≫ U.hom)).toPresheafFiber U
      (Over.homMk b rfl) G.obj) := by
  subst s
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A module sheaf over a finite commutative ring on a Noetherian scheme is finite locally
constant if its geometric stalks are finite sets and all strict-localization specialization
maps are bijective. The conclusion gives the finite module and trivialization on every
member of a jointly surjective étale cover, using restriction to the localized site.
Source: Stacks Project, Tag 0GKC, lemma-characterize-locally-constant-module, (2) implies (1)
(blueprint: lem-weil-pbc-etale-finite-stalk-specialization-criterion).

Proof:
1. At each ordinary point choose its algebraically closed geometric point and let M
be its finite stalk. Lift its identity to a linear map into sections on one pointed
etale neighbourhood, using the finite addition and scalar-multiplication tables
(`lem-weil-pbc-etale-finite-stalk-local-presentation`).
2. The locus on this neighbourhood where the linear section map induces a bijection
on geometric stalks is independent of the chosen geometric point and invariant under
specialization in both directions. Indeed, the strict-localization germ calculation
expresses one germ map as the other followed by a bijective specialization map
(`lem-weil-pbc-etale-section-germ-specialization`).
3. Restrict to an affine open through the chosen lift. This affine scheme is Noetherian
since its map to S is locally of finite type. Its finitely many irreducible components
have generic points. Removing the components not containing the lift gives an open
neighbourhood inside the bijectivity locus
(`lem-weil-pbc-specialization-invariant-neighborhood`).
4. Restrict the section map to this open. Its constant-sheaf adjunct is an isomorphism
because every geometric stalk map is bijective
(`lem-weil-pbc-etale-section-germ-iso`). The original finite stalk is its constant module.
These neighbourhoods form a jointly surjective etale cover indexed by the points of S;
when S is empty this same construction is the empty cover. -/
theorem finiteLocallyConstant_of_finite_stalks_of_bijective_specialization
    {S : Scheme.{u}} [IsNoetherian S]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
      Finite (↑((pointSmallEtale s).sheafFiber.obj G) : Type (u + 1)))
    (hsp : ∀ (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
      (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ξ) ⟶ strictHenselizationScheme s),
      Function.Bijective (etaleModuleStalkSpecialization s t G)) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage S, ∀ i : 𝒰.I₀,
      ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
        Nonempty ((G.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf (S.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  have local_model (x : S) :
      ∃ (U : S.Etale) (y : U.left), U.hom y = x ∧
        ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty (G.over U ≅
            (constantSheaf (S.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M) := by
    let s := S.algClosurePoint x
    have := hfinite (AlgebraicClosure (S.residueField x)) s
    let M := (pointSmallEtale s).sheafFiber.obj G
    obtain ⟨U, a, f, hf⟩ := exists_etale_finite_stalk_section G s
    let E : Set U.left := {z | Function.Bijective
      (f ≫ (pointSmallEtale (U.left.algClosurePoint z ≫ U.hom)).toPresheafFiber U
        (Over.homMk (U.left.algClosurePoint z) rfl) G.obj)}
    have hE (z w : U.left) (hzw : z ⤳ w) : z ∈ E ↔ w ∈ E := by
      exact etale_section_germ_bijective_specializes_iff G hsp U M f
        (U.left.algClosurePoint z) (U.left.algClosurePoint w) (by simpa using hzw)
    let u := a.left (IsLocalRing.closedPoint _)
    have hu : u ∈ E := by
      have hid : Function.Bijective (f ≫ (pointSmallEtale s).toPresheafFiber U a G.obj) := by
        rw [hf]
        exact Function.bijective_id
      have ha : a.left ≫ U.hom = s := a.w
      have hid' : Function.Bijective
          (f ≫ (pointSmallEtale (a.left ≫ U.hom)).toPresheafFiber U
            (Over.homMk a.left rfl) G.obj) := by
        exact (sectionGerm_bijective_normalize G U M f s a.left a.w).mp hid
      exact (etale_section_germ_bijective_specializes_iff G hsp U M f
        a.left (U.left.algClosurePoint u) (by simpa [u] using specializes_refl u)).mp hid'
    obtain ⟨i, v, hv⟩ := U.left.affineCover.exists_eq u
    let A := U.left.affineCover.X i
    let j : A ⟶ U.left := U.left.affineCover.f i
    have : IsLocallyNoetherian A := by
      have hj : LocallyOfFiniteType (j ≫ U.hom) := inferInstance
      exact LocallyOfFiniteType.isLocallyNoetherian (Y := S) (j ≫ U.hom)
    have : IsNoetherian A := { }
    obtain ⟨V, hvV, hV⟩ := exists_open_subset_of_specialization_invariant
      (finite_irreducibleComponents_of_isNoetherian (X := A)) (j ⁻¹' E)
      (fun z w hzw ↦ hE (j z) (j w) (hzw.map j.continuous)) v (by
        change j v ∈ E
        rw [show j v = u from hv]
        exact hu)
    let W : S.Etale := Etale.mk ((Scheme.Opens.ι (X := A) V) ≫ j ≫ U.hom)
    let g : W ⟶ U := MorphismProperty.Over.homMk ((Scheme.Opens.ι (X := A) V) ≫ j) (by simp [W])
    let fW : M ⟶ G.obj.obj (Opposite.op W) := f ≫ G.obj.map g.op
    have hgerm (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ W.left) :
        Function.Bijective (fW ≫ (pointSmallEtale (b ≫ W.hom)).toPresheafFiber W
          (Over.homMk b rfl) G.obj) := by
      let c : Spec (.of Ω) ⟶ U.left := b ≫ g.left
      have hcE : c (IsLocalRing.closedPoint Ω) ∈ E := by
        exact hV (b (IsLocalRing.closedPoint Ω)).property
      have hc := (etale_section_germ_bijective_specializes_iff G hsp U M f
        c (U.left.algClosurePoint (c (IsLocalRing.closedPoint Ω)))
        (by simpa using specializes_refl (c (IsLocalRing.closedPoint Ω)))).mpr hcE
      have hw : g.left ≫ U.hom = W.hom := g.w
      have hb : (b ≫ g.left) ≫ U.hom = b ≫ W.hom := by rw [Category.assoc, hw]
      dsimp only [fW]
      rw [Category.assoc, (pointSmallEtale (b ≫ W.hom)).toPresheafFiber_w]
      change Function.Bijective (f ≫ (pointSmallEtale (b ≫ W.hom)).toPresheafFiber U
        (Over.homMk (b ≫ g.left) hb) G.obj)
      exact (sectionGerm_bijective_normalize G U M f (b ≫ W.hom)
        (b ≫ g.left) hb).mpr hc
    refine ⟨W, ⟨v, hvV⟩, ?_, M, inferInstance, ?_⟩
    · change U.hom (j v) = x
      rw [show j v = u from hv]
      change U.hom (a.left (IsLocalRing.closedPoint _)) = x
      have ha : a.left ≫ U.hom = s := a.w
      have hh := congrArg (fun q : Spec (.of (AlgebraicClosure (S.residueField x))) ⟶ S ↦
        q (IsLocalRing.closedPoint _)) ha
      exact hh.trans (by simp [s])
    · exact exists_constant_iso_of_bijective_section_germs G W M fW hgerm
  choose U y hy M hM e using local_model
  let 𝒰 : Cover.{u} etalePrecoverage S :=
    { I₀ := S
      X x := (U x).left
      f x := (U x).hom
      mem₀ := by
        exact (presieve₀_mem_precoverage_iff _).mpr
          ⟨fun x ↦ ⟨x, y x, hy x⟩, fun x ↦ (U x).prop⟩ }
  exact ⟨𝒰, fun x ↦ ⟨M x, hM x, e x⟩⟩

end AlgebraicGeometry.Scheme
