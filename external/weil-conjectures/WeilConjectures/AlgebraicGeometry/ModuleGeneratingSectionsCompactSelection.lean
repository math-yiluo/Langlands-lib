/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.AlgebraicGeometry.ModuleGeneratingSectionsLocalSelection
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Selecting generators on a compact open

Source: Stacks Project, Modules, Lemma 01BB, finite-cover argument.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem epi_overMap_iff_local_lifts
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    {F G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)} (φ : F ⟶ G) :
    Epi ((overMap (moduleRings X.toRingedSpace) (homOfLE hKV)).map φ) ↔
      ∀ (W : X.Opens) (hWK : W ≤ K)
        (t : G.val.obj (.op (Over.mk (homOfLE (hWK.trans hKV)))))
        (x : X), x ∈ W →
        ∃ (Z : X.Opens) (hZW : Z ≤ W), x ∈ Z ∧
          ∃ s : F.val.obj (.op (Over.mk (homOfLE (hZW.trans (hWK.trans hKV))))),
            φ.val.app _ s = G.val.map
              (Over.homMk (homOfLE hZW)).op t := by
  let T := SheafOfModules.toSheaf.{u} ((moduleRings X.toRingedSpace).over K)
  let ψ := (overMap (moduleRings X.toRingedSpace) (homOfLE hKV)).map φ
  rw [← T.epi_map_iff_epi ψ, ← CategoryTheory.Sheaf.isLocallySurjective_iff_epi']
  constructor
  · intro h W hWK t x hx
    have hh := CategoryTheory.Presheaf.imageSieve_mem
      ((Opens.grothendieckTopology X).over K) (T.map ψ).hom
      (U := .op (Over.mk (homOfLE hWK))) t
    change Sieve.overEquiv (Over.mk (homOfLE hWK)) _ ∈
      Opens.grothendieckTopology X W at hh
    obtain ⟨Z, f, hf, hxZ⟩ := hh x hx
    rw [Sieve.overEquiv_iff] at hf
    exact ⟨Z, leOfHom f, hxZ, hf⟩
  · intro h
    constructor
    intro W t
    change Sieve.overEquiv W _ ∈ Opens.grothendieckTopology X W.left
    intro x hx
    obtain ⟨Z, hZW, hxZ, s, hs⟩ := h W.left (leOfHom W.hom) t x hx
    refine ⟨Z, homOfLE hZW, ?_, hxZ⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨s, hs⟩

-- Epimorphy can be checked on an open cover before specializing the source to a free sheaf.
private theorem epi_overMap_of_open_cover
    (X : Scheme.{u}) (V K : X.Opens) (hKV : K ≤ V)
    {F G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)} (φ : F ⟶ G)
    {I : Type*} (U : I → X.Opens) (hUK : ∀ i, U i ≤ K)
    (hcover : (K : Set X) ⊆ ⋃ i, (U i : Set X))
    (hU : ∀ i, Epi ((overMap (moduleRings X.toRingedSpace)
      (homOfLE ((hUK i).trans hKV))).map φ)) :
    Epi ((overMap (moduleRings X.toRingedSpace) (homOfLE hKV)).map φ) := by
  apply (epi_overMap_iff_local_lifts X V K hKV φ).mpr
  intro W hWK a x hxW
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover (hWK hxW))
  have he := hU i
  let Q := W ⊓ U i
  have hQV : Q ≤ V := inf_le_left.trans (hWK.trans hKV)
  let r : Over.mk (homOfLE hQV) ⟶ Over.mk (homOfLE (hWK.trans hKV)) :=
    Over.homMk (homOfLE inf_le_left)
  let b : G.val.obj (.op (Over.mk (homOfLE hQV))) := G.val.map r.op a
  obtain ⟨Z, hZQ, hxZ, z, hz⟩ :=
    (epi_overMap_iff_local_lifts X V (U i) ((hUK i).trans hKV) _).mp he
      Q inf_le_right b x ⟨hxW, hxi⟩
  refine ⟨Z, hZQ.trans inf_le_left, hxZ, z, ?_⟩
  change _ = G.val.presheaf.map (Over.homMk (homOfLE hZQ)).op
    (G.val.presheaf.map
      (Over.homMk (homOfLE (show Q ≤ W from inf_le_left))).op a) at hz
  change _ = G.val.presheaf.map
    (Over.homMk (homOfLE (hZQ.trans inf_le_left))).op a
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    ← Over.homMk_comp, homOfLE_comp] using hz

-- Elaborating free coproduct maps across slice restriction needs additional steps.
set_option backward.isDefEq.respectTransparency false in
private theorem freeMap_subset_epi
    (X : Scheme.{u}) (V U : X.Opens) (hUV : U ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (σ : (H.over V).GeneratingSections) (S T : Finset σ.I) (hST : S ⊆ T)
    (hS : Epi ((overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).map
      (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : S → σ.I) ≫ σ.π))) :
    Epi ((overMap (moduleRings X.toRingedSpace) (homOfLE hUV)).map
      (freeMap (R := (moduleRings X.toRingedSpace).over V) ((↑) : T → σ.I) ≫ σ.π)) := by
  let f : S → T := fun i ↦ ⟨i.val, hST i.property⟩
  have hf : freeMap (R := (moduleRings X.toRingedSpace).over V) f ≫
      freeMap ((↑) : T → σ.I) = freeMap ((↑) : S → σ.I) := by
    apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext (isColimitFreeCofan S)
    intro i
    simp [f]
  let F := overMap (moduleRings X.toRingedSpace) (homOfLE hUV)
  have hfac : F.map (freeMap f) ≫ F.map (freeMap ((↑) : T → σ.I) ≫ σ.π) =
      F.map (freeMap ((↑) : S → σ.I) ≫ σ.π) := by
    rw [← F.map_comp, ← Category.assoc, hf]
  have := hS
  exact epi_of_epi_fac hfac

-- The slice-site section types require additional elaboration steps.
set_option backward.isDefEq.respectTransparency false in
/-- A specified global generating family has a finite subfamily generating on a
compact open where the module is of finite type. No affineness or quasi-coherence
is assumed: the global generating family is an explicit hypothesis.

Source: Stacks Project, Modules, Lemma 01BB, proof, applied to the directed
family of subsheaves generated by finite subsets of the specified generators;
Lemma 01B8 gives the local surjectivity neighbourhoods.
https://stacks.math.columbia.edu/tag/01BB
(blueprint: lem-weil-pbc-module-generating-sections-compact-selection).

Proof: At x in K choose a finite local generating family for H on a neighbourhood
inside K. The epimorphism defined by sigma lifts these generators locally to the
free sheaf on sigma.I. A stalk of this free sheaf is the direct sum of copies of
the local ring, so these finitely many lifts involve only a finite subset S_x of
sigma.I. The free map for S_x is therefore surjective at x. By Lemma 01B8,
shrink the neighbourhood so that it is surjective there, using finite type of
the target. These neighbourhoods cover K. Compactness selects finitely many;
take S to be the union of their finite subsets S_x. On each selected
neighbourhood the S_x map factors through the S map, so the S map is epi there.
Surjectivity of sheaves is local, hence its restriction to K is epi. This is
also the proof of 01BB applied to the directed union of the finite generated
image subsheaves: their union is H because sigma generates. Slice restriction
agrees with ordinary restriction and preserves free sheaves and the unit.
If K is empty, take S empty; every module sheaf on the empty open is zero.
If sigma.I is empty, sigma already exhibits the target as zero, so S empty
works on every K. No choice of generators of an unknown affine module remains.
-/
theorem exists_finset_generatingSections_on_compact
    (X : Scheme.{u}) (V K : X.Opens) (hK : IsCompact (K : Set X)) (hKV : K ≤ V)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [(H.over K).IsFiniteType] (σ : (H.over V).GeneratingSections) :
    ∃ S : Finset σ.I,
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hKV)).map
        (SheafOfModules.freeMap (R := (moduleRings X.toRingedSpace).over V)
          ((↑) : S → σ.I) ≫ σ.π)) := by
  classical
  choose U hUK hx S hS using exists_finset_generatingSections_near_point X V K hKV H σ
  have hcover : (K : Set X) ⊆ ⋃ x : K, (U x : Set X) := by
    intro x hxK
    exact Set.mem_iUnion.mpr ⟨⟨x, hxK⟩, hx ⟨x, hxK⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ (U x : Set X))
    (fun x ↦ (U x).isOpen) hcover
  let T : Finset σ.I := t.biUnion S
  refine ⟨T, ?_⟩
  apply epi_overMap_of_open_cover X V K hKV _ (fun i : t ↦ U i) (fun i ↦ hUK i)
  · intro x hxK
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht hxK)
    obtain ⟨hit, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i, hit⟩, hxi⟩
  · intro i
    exact freeMap_subset_epi X V (U i) ((hUK i).trans hKV) H σ (S i) T
      (fun j hj ↦ Finset.mem_biUnion.mpr ⟨i, i.property, hj⟩) (hS i)

end AlgebraicGeometry.Scheme.Modules
