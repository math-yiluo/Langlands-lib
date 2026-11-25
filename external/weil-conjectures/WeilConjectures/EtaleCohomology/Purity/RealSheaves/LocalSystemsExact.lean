/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# Exactness of the Galois correspondence for finite local systems

Finite locally constant sheaves of `Λ`-modules on the small étale site of a scheme, for a finite
ring `Λ`, form an abelian full subcategory of all sheaves of `Λ`-modules: they contain zero and
are closed under kernels, cokernels and finite direct sums
(`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.kernel`,
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.cokernel`). Likewise finite continuous
representations of a topological group form an abelian full subcategory of `Rep Λ G`. Hence
every equivalence between the two, in particular the Galois correspondence
`AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf`, is exact: it matches
short exact sequences of sheaves with short exact sequences of representations
(`AlgebraicGeometry.Scheme.isFiniteLocallyConstantSheaf_shortExact_iff`).
-/

@[expose] public section

universe v w u

open CategoryTheory Limits ZeroObject

namespace Rep

variable {Λ : Type v} [CommRing Λ] {G : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The stabilizer `{g | ρ g v = v}` of a vector is open as soon as it contains an open
neighbourhood of `1`: it is then a union of translates of that neighbourhood. -/
lemma isOpen_setOf_apply_eq_of_subset {V : Type*} [AddCommGroup V] [Module Λ V]
    (ρ : Representation Λ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S)
    (hSv : ∀ h ∈ S, ρ h v = v) : IsOpen {g : G | ρ g v = v} := by
  refine isOpen_iff_forall_mem_open.2 fun g₀ hg₀ ↦ ⟨(g₀ * ·) '' S, ?_,
    (Homeomorph.mulLeft g₀).isOpenMap S hS, ⟨1, h1, mul_one g₀⟩⟩
  rintro _ ⟨h, hh, rfl⟩
  simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply, hSv h hh]
  exact hg₀

instance isFiniteContinuous_isClosedUnderSubobjects :
    (IsFiniteContinuous (Λ := Λ) (G := G)).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    obtain ⟨_, hY⟩ := hY
    have hf : Function.Injective f.hom := (Rep.mono_iff_injective f).1 inferInstance
    refine ⟨Finite.of_injective _ hf, fun x ↦ ?_⟩
    convert hY (f.hom x) using 1
    ext g
    simp only [Set.mem_ofPred_eq, ← Rep.hom_comm_apply, hf.eq_iff]

instance isFiniteContinuous_isClosedUnderQuotients :
    (IsFiniteContinuous (Λ := Λ) (G := G)).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    obtain ⟨_, hX⟩ := hX
    have hf : Function.Surjective f.hom := (Rep.epi_iff_surjective f).1 inferInstance
    refine ⟨Finite.of_surjective _ hf, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hf y
    refine isOpen_setOf_apply_eq_of_subset _ _ (hX x) (by simp) fun h hh ↦ ?_
    rw [← Rep.hom_comm_apply, show X.ρ h x = x from hh]

instance isFiniteContinuous_isClosedUnderIsomorphisms :
    (IsFiniteContinuous (Λ := Λ) (G := G)).IsClosedUnderIsomorphisms where
  of_iso e h := (IsFiniteContinuous (Λ := Λ) (G := G)).prop_of_mono e.inv h

instance isFiniteContinuous_containsZero :
    (IsFiniteContinuous (Λ := Λ) (G := G)).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, ?_⟩
    have : Subsingleton (0 : Rep.{v} Λ G).V :=
      ModuleCat.subsingleton_of_isZero
        ((forget₂ (Rep.{v} Λ G) (ModuleCat.{v} Λ)).map_isZero (isZero_zero _))
    refine ⟨Finite.of_subsingleton, fun x ↦ ?_⟩
    convert isOpen_univ
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _

/-- A direct sum of finite continuous representations is finite continuous. -/
theorem IsFiniteContinuous.biprod {X Y : Rep.{v} Λ G} (hX : IsFiniteContinuous X)
    (hY : IsFiniteContinuous Y) : IsFiniteContinuous (X ⊞ Y) := by
  obtain ⟨_, hX⟩ := hX
  obtain ⟨_, hY⟩ := hY
  have htot (v : (X ⊞ Y).V) : (biprod.inl : X ⟶ X ⊞ Y).hom ((biprod.fst : X ⊞ Y ⟶ X).hom v) +
      (biprod.inr : Y ⟶ X ⊞ Y).hom ((biprod.snd : X ⊞ Y ⟶ Y).hom v) = v := by
    have h := congrArg (fun f : X ⊞ Y ⟶ X ⊞ Y ↦ f.hom v) (biprod.total (X := X) (Y := Y))
    simp only [Rep.add_hom, Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.coe_add,
      Pi.add_apply,
      Representation.IntertwiningMap.comp_apply, Representation.IntertwiningMap.id_apply] at h
    exact h
  have hinj : Function.Injective fun v : (X ⊞ Y).V ↦
      ((biprod.fst : X ⊞ Y ⟶ X).hom v, (biprod.snd : X ⊞ Y ⟶ Y).hom v) := by
    intro v w h
    simp only [Prod.mk.injEq] at h
    rw [← htot v, ← htot w, h.1, h.2]
  refine ⟨Finite.of_injective _ hinj, fun v ↦ ?_⟩
  refine isOpen_setOf_apply_eq_of_subset _ _
    ((hX ((biprod.fst : X ⊞ Y ⟶ X).hom v)).inter (hY ((biprod.snd : X ⊞ Y ⟶ Y).hom v)))
    (by simp) fun h hh ↦ ?_
  have e₁ (a : X.V) : (X ⊞ Y).ρ h ((biprod.inl : X ⟶ X ⊞ Y).hom a) =
      (biprod.inl : X ⟶ X ⊞ Y).hom (X.ρ h a) := (Rep.hom_comm_apply _ _ _).symm
  have e₂ (a : Y.V) : (X ⊞ Y).ρ h ((biprod.inr : Y ⟶ X ⊞ Y).hom a) =
      (biprod.inr : Y ⟶ X ⊞ Y).hom (Y.ρ h a) := (Rep.hom_comm_apply _ _ _).symm
  have h₁ : X.ρ h ((biprod.fst : X ⊞ Y ⟶ X).hom v) = (biprod.fst : X ⊞ Y ⟶ X).hom v := hh.1
  have h₂ : Y.ρ h ((biprod.snd : X ⊞ Y ⟶ Y).hom v) = (biprod.snd : X ⊞ Y ⟶ Y).hom v := hh.2
  calc (X ⊞ Y).ρ h v = (X ⊞ Y).ρ h
        ((biprod.inl : X ⟶ X ⊞ Y).hom ((biprod.fst : X ⊞ Y ⟶ X).hom v) +
        (biprod.inr : Y ⟶ X ⊞ Y).hom ((biprod.snd : X ⊞ Y ⟶ Y).hom v)) := by rw [htot]
    _ = v := by rw [map_add, e₁, e₂, h₁, h₂, htot]

instance isFiniteContinuous_isClosedUnderFiniteProducts :
    (IsFiniteContinuous (Λ := Λ) (G := G)).IsClosedUnderFiniteProducts :=
  have : (IsFiniteContinuous (Λ := Λ) (G := G)).IsClosedUnderBinaryProducts :=
    .mk' (by
      rintro _ ⟨F, hF⟩
      exact (IsFiniteContinuous (Λ := Λ) (G := G)).prop_of_iso
        ((biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
        (IsFiniteContinuous.biprod (hF ⟨.left⟩) (hF ⟨.right⟩)))
  .mk'

end Rep

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The property of a sheaf of `Λ`-modules on `Y_ét` of being finite locally constant. -/
abbrev isFiniteLocallyConstantSheaf (Y : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :
    ObjectProperty (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsFiniteLocallyConstantSheaf F

instance : (isFiniteLocallyConstantSheaf Y Λ).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have : IsFiniteLocallyConstantSheaf _ := h
    exact IsFiniteLocallyConstantSheaf.of_iso e

instance : (isFiniteLocallyConstantSheaf Y Λ).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _)⟩

instance : (isFiniteLocallyConstantSheaf Y Λ).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have : IsFiniteLocallyConstantSheaf _ := hX
    have : IsFiniteLocallyConstantSheaf _ := hY
    have := IsFiniteLocallyConstantSheaf.kernel f
    exact IsFiniteLocallyConstantSheaf.of_iso (F := kernel f)
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _) hk)

instance : (isFiniteLocallyConstantSheaf Y Λ).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    have : IsFiniteLocallyConstantSheaf _ := hX
    have : IsFiniteLocallyConstantSheaf _ := hY
    have := IsFiniteLocallyConstantSheaf.cokernel f
    exact IsFiniteLocallyConstantSheaf.of_iso (F := cokernel f)
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hk)

instance : (isFiniteLocallyConstantSheaf Y Λ).IsClosedUnderFiniteProducts :=
  have : (isFiniteLocallyConstantSheaf Y Λ).IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨G, hG⟩
    have : IsFiniteLocallyConstantSheaf (G.obj ⟨.left⟩) := hG _
    have : IsFiniteLocallyConstantSheaf (G.obj ⟨.right⟩) := hG _
    have := IsFiniteLocallyConstantSheaf.biprod (G.obj ⟨.left⟩) (G.obj ⟨.right⟩)
    exact IsFiniteLocallyConstantSheaf.of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair G)).symm))
  .mk'

/-- Blueprint `proposition-lattices-representations-normal-scheme`: Galois correspondence for finite
local systems, exactness.

Every equivalence `e` between finite locally constant sheaves of `Λ`-modules on `Y_ét` and finite
continuous `Λ`-representations of a topological group `G` — such as the Galois correspondence
`AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf_of_isFundamentalGroup`
— is exact: a short complex of finite locally constant sheaves is short exact as a complex of
sheaves if and only if its image is short exact as a complex of representations. Both sides
are abelian full subcategories closed under kernels, cokernels and finite direct sums, so their
inclusions are exact, and an equivalence of abelian categories is exact. -/
theorem isFiniteLocallyConstantSheaf_shortExact_iff (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (e : ObjectProperty.FullSubcategory
          (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
            IsFiniteLocallyConstantSheaf F) ≌
        ObjectProperty.FullSubcategory (Rep.IsFiniteContinuous (Λ := Λ) (G := G)))
    (S : ShortComplex (ObjectProperty.FullSubcategory
      (fun F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteLocallyConstantSheaf F))) :
    (S.map (ObjectProperty.ι _)).ShortExact ↔
      (S.map (e.functor ⋙ ObjectProperty.ι _)).ShortExact :=
  ObjectProperty.shortExact_map_ι_iff_of_equivalence (P := isFiniteLocallyConstantSheaf Y Λ) e S

end AlgebraicGeometry.Scheme
