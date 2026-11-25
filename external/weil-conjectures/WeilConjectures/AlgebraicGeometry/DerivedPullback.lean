/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Pullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategoryComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.InverseImageExactKFlat
import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.IrreducibleDef
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Derived pullback of modules on schemes

For a morphism of schemes `g : T ⟶ S`, the derived pullback `Lg^* : D(𝒪_S) ⥤ D(𝒪_T)` on the
model `schemeDerivedCategory` of the derived category is `Scheme.Modules.derivedPullback g`, the
left derived functor of `Scheme.Modules.pullback g`, transported along the equivalences
`schemeDerivedCategoryEquiv : schemeDerivedCategory X ≌ DerivedCategory X.Modules`.

The tensor pullback `𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹(-)` (`Scheme.Modules.tensorPullback g`) is isomorphic
to `Scheme.Modules.pullback g`, as both are left adjoint to the pushforward. Hence
`derivedPullback g` is also a left derived functor of the tensor pullback, and its counit is an
isomorphism on K-flat complexes: on a K-flat resolution `P ⟶ E` it is represented by
`𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P` (`AlgebraicGeometry.derivedPullback_spec`).

## Main definitions

* `AlgebraicGeometry.derivedPullback g`: the derived pullback on `schemeDerivedCategory`.
* `AlgebraicGeometry.derivedPullbackCounit g`: its counit, with respect to the pullback
  `Scheme.Modules.pullback g`.
* `AlgebraicGeometry.derivedPullbackIso g`: the comparison isomorphism with
  `Scheme.Modules.derivedPullback g` across `schemeDerivedCategoryEquiv`.

## Main statements

* `AlgebraicGeometry.derivedPullback_spec`: `derivedPullback g` is a triangulated left derived
  functor of the tensor pullback, with counit invertible on K-flat complexes.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Existence of a left derived functor of the tensor pullback along a morphism of schemes,
constructed from K-flat resolutions.

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  det-thm-picard-semicon/def-pc-derived-pullback.md, node
  lemma-coherent-base-change-invertible-sheaves--2; the functor is `L g^* = L(g^sharp)^* ∘ g⁻¹`, and
  on a K-flat resolution `P ⟶ E` it is represented by `𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P`.
The functor `I` is the exact module inverse image, and `E` is the recorded tensor
pullback, on the shared module-sheaf category instances. The universal property and
K-flat counit specify the derived composite uniquely up to canonical isomorphism.
Source: Stacks Project, Cohomology, Tags 06YI and 06YJ.
Proof (the three steps of the node):
1. The inverse-image stalk isomorphism (lem-weil-pbc-topological-inverse-image-stalk)
   and stalkwise exactness show that `I` is exact and preserves quasi-isomorphisms
   (def-pc-quasi-iso-modules), hence induces a functor on derived categories.
2. Apply lem-pur-derived-change-of-rings to `tensorPullbackRingMap g`. Compose its
   derived functor with derived inverse image. Termwise the composite is the recorded
   `tensorPullback g`; the resolving-class universal property gives the counit below.
3. Choose a K-flat resolution (lem-pc-kflat-resolution). Inverse image preserves its
   quasi-isomorphism by step 1 and its K-flatness by lem-pc-kflat-pullback-preservation
   applied to `(T, g⁻¹𝒪_S) → (S, 𝒪_S)`. The change-of-rings counit is therefore an
   isomorphism. The canonical comparison for `s : P → G` is the inverse of `L(Q(s))`
   followed by this counit at `P`. Comparisons between resolutions factor through
   `L(Q(G))`, so are independent of choices and compatible with composition.
(blueprint: lemma-coherent-base-change-invertible-sheaves--2). -/
theorem exists_derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    ∃ L : schemeDerivedCategory S ⥤ schemeDerivedCategory T,
      ∃ (I : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
          SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
        (hI : ∀ M, I.obj M = TopCat.Sheaf.inverseImageModule g.base S.sheaf M)
        (_ : ∀ {M N} (a : M ⟶ N),
          I.map a = eqToHom (hI M) ≫
            TopCat.Sheaf.inverseImageModuleMap g.base S.sheaf M a ≫
              eqToHom (hI N).symm)
        (_ : I.Additive),
        PreservesFiniteLimits I ∧ PreservesFiniteColimits I ∧
        (∀ {P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
          (s : P ⟶ G), CochainComplex.IsKFlatTensorResolution (R := S.sheaf) s →
            CochainComplex.IsKFlatTensorResolution
              (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf)
              ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
        ∃ (E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings T.toRingedSpace))
          (h : ∀ M, E.obj M = Scheme.Modules.tensorPullbackObj g M)
          (_ : ∀ {M N} (a : M ⟶ N),
            E.map a = eqToHom (h M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
              eqToHom (h N).symm)
          (_ : E.Additive)
          (ε : DerivedCategory.Qh ⋙ L ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          L.IsLeftDerivedFunctor ε
              (HomotopyCategory.quasiIso
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
            (∃ (_ : L.CommShift ℤ), L.IsTriangulated) ∧
            ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ,
              CochainComplex.IsKFlatTensor (R := S.sheaf) P →
                IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres⟩ :=
    exists_inverseImage_exact_kFlat g
  let E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
  let : E.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  let : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ E
    (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have : F.IsTriangulated := by
    dsimp only [F]
    set_option synthInstance.maxSize 512 in infer_instance
  let C : Set (HomotopyCategory A (ComplexShape.up ℤ)) :=
    {X | ∃ P : CochainComplex A ℤ,
      CochainComplex.IsKFlatTensor (R := S.sheaf) P ∧ q.obj P = X}
  have hres : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X' ⟶ X),
        X' ∈ C ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := S.sheaf) G
    refine ⟨q.obj P, q.map s, ⟨P, hP, rfl⟩, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  have hinv : ∀ (X X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X ⟶ X'),
      X ∈ C → X' ∈ C → HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s →
        IsIso (F.map s) := by
    intro X X' s hX hX' hs
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨P', hP', rfl⟩ := hX'
    obtain ⟨s, rfl⟩ := q.map_surjective s
    have hsq : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := tensorPullback_quasiIso_of_isKFlat g s hP hP' hsq
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map s)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, L, ε, hL, htri, hε⟩ :=
    CategoryTheory.Functor.leftDerived_from_resolvingClass A
      (schemeDerivedCategory T) F C hres hinv
  refine ⟨L, I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, (fun _ ↦ rfl), ?_, inferInstance, ε, hL, htri, ?_⟩
  · intro M N a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro P hP
    exact hε (q.obj P) ⟨P, hP, rfl⟩

/-- The tensor pullback and the pullback of modules are isomorphic: both are left adjoint to the
pushforward. -/
theorem nonempty_tensorPullbackIsoPullback {T S : Scheme.{u}} (g : T ⟶ S) :
    Nonempty (Scheme.Modules.tensorPullback g ≅ Scheme.Modules.pullback g) := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
  exact ⟨adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction g)⟩

section

variable {T S : Scheme.{u}} (g : T ⟶ S)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]

/-- The derived pullback `L g^* : D(𝒪_S) ⥤ D(𝒪_T)` on `schemeDerivedCategory`: the left derived
functor `Scheme.Modules.derivedPullback g` of the pullback of modules, transported along
`schemeDerivedCategoryEquiv`. It is isomorphic to `Scheme.Modules.derivedPullback g` across
these equivalences (`AlgebraicGeometry.derivedPullbackIso`), and it is a left derived functor of
the tensor pullback whose counit is an isomorphism on K-flat complexes
(`AlgebraicGeometry.derivedPullback_spec`).

(blueprint: lemma-coherent-base-change-invertible-sheaves--2) -/
noncomputable irreducible_def derivedPullback :
    schemeDerivedCategory.{u, w} S ⥤ schemeDerivedCategory.{u, w} T :=
  (schemeDerivedCategoryEquiv S).functor ⋙ Scheme.Modules.derivedPullback g ⋙
    (schemeDerivedCategoryEquiv T).inverse

/-- The comparison isomorphism between `derivedPullback g` and `Scheme.Modules.derivedPullback g`
across the equivalences `schemeDerivedCategoryEquiv`. -/
noncomputable def derivedPullbackIso :
    (schemeDerivedCategoryEquiv.{w} S).inverse ⋙ derivedPullback.{u, w} g ⋙
        (schemeDerivedCategoryEquiv.{w} T).functor ≅ Scheme.Modules.derivedPullback g :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (eqToIso (derivedPullback_def g)) _) ≪≫
  Functor.isoWhiskerRight (schemeDerivedCategoryEquiv S).counitIso
      (Scheme.Modules.derivedPullback g ⋙ (schemeDerivedCategoryEquiv T).inverse ⋙
        (schemeDerivedCategoryEquiv T).functor) ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.derivedPullback g)
      (schemeDerivedCategoryEquiv T).counitIso

/-- The pullback of modules on homotopy categories, on the homotopy categories of
`SheafOfModules (moduleRings _)`. -/
noncomputable abbrev pullbackHomotopyCategory :
    HomotopyCategory (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (ComplexShape.up ℤ) :=
  (Scheme.Modules.pullback g).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The counit of `Scheme.Modules.derivedPullback g`, on the homotopy category of
`SheafOfModules (moduleRings S.toRingedSpace)`. -/
noncomputable def modulesDerivedPullbackCounit :
    modulesQh S ⋙ Scheme.Modules.derivedPullback g ⟶ pullbackHomotopyCategory g ⋙ modulesQh T :=
  Scheme.Modules.derivedPullbackCounit g

instance : (Scheme.Modules.derivedPullback g).IsLeftDerivedFunctor
    (modulesDerivedPullbackCounit g)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings S.toRingedSpace))
      (ComplexShape.up ℤ)) :=
  inferInstanceAs ((Scheme.Modules.derivedPullback g).IsLeftDerivedFunctor
    (Scheme.Modules.derivedPullbackCounit g) (HomotopyCategory.quasiIso S.Modules _))

/-- The counit of the composite `(schemeDerivedCategoryEquiv S).functor ⋙
Scheme.Modules.derivedPullback g ⋙ (schemeDerivedCategoryEquiv T).inverse`. -/
noncomputable def derivedPullbackModelCounit :
    DerivedCategory.Qh ⋙ ((schemeDerivedCategoryEquiv S).functor ⋙
        Scheme.Modules.derivedPullback g ⋙ (schemeDerivedCategoryEquiv.{w} T).inverse) ⟶
      (pullbackHomotopyCategory g ⋙ modulesQh T) ⋙ (schemeDerivedCategoryEquiv.{w} T).inverse :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (qhCompSchemeDerivedCategoryEquivFunctor S).hom _ ≫
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (modulesDerivedPullbackCounit g) _)

/-- The counit `Lg^*(E) ⟶ g^* E` of `derivedPullback g`, for the pullback of modules. -/
noncomputable def derivedPullbackCounit :
    DerivedCategory.Qh ⋙ derivedPullback.{u, w} g ⟶
      (pullbackHomotopyCategory g ⋙ modulesQh T) ⋙ (schemeDerivedCategoryEquiv.{w} T).inverse :=
  Functor.whiskerLeft _ (eqToHom (derivedPullback_def g)) ≫ derivedPullbackModelCounit g

instance : (derivedPullback.{u, w} g).IsLeftDerivedFunctor (derivedPullbackCounit.{u, w} g)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings S.toRingedSpace))
      (ComplexShape.up ℤ)) := by
  have := Functor.isLeftDerivedFunctor_comp_of_isEquivalence _
    (modulesDerivedPullbackCounit g)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings S.toRingedSpace))
      (ComplexShape.up ℤ)) (schemeDerivedCategoryEquiv.{w} T).inverse
  have h : ((schemeDerivedCategoryEquiv S).functor ⋙ Scheme.Modules.derivedPullback g ⋙
      (schemeDerivedCategoryEquiv.{w} T).inverse).IsLeftDerivedFunctor
      (derivedPullbackModelCounit g)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings S.toRingedSpace))
        (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_precomp_of_isEquivalence
      (schemeDerivedCategoryEquiv S).functor (qhCompSchemeDerivedCategoryEquivFunctor S) _ _
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings S.toRingedSpace))
          (ComplexShape.up ℤ))
  exact (Functor.isLeftDerivedFunctor_iff_of_iso (α := derivedPullbackCounit g)
    (α' := derivedPullbackModelCounit g) (e := eqToIso (derivedPullback_def g))
    (comm := rfl) ..).2 h

/-- **The derived pullback is the left derived functor of the tensor pullback.** For
`g : T ⟶ S`, `derivedPullback g` is a triangulated left derived functor of the tensor pullback
`E = Scheme.Modules.tensorPullback g` (with the exact inverse image `I` underlying it), and its
counit `Lg^*(P) ⟶ E(P)` is an isomorphism for every K-flat complex `P`.
Proof: `derivedPullback g` and the functor of `exists_derivedPullback` are left derived
functors of isomorphic functors, as `E ≅ Scheme.Modules.pullback g`; hence they are isomorphic,
and the properties of the latter transfer.

(blueprint: lemma-coherent-base-change-invertible-sheaves--2) -/
theorem derivedPullback_spec :
    ∃ (I : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
          SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
        (hI : ∀ M, I.obj M = TopCat.Sheaf.inverseImageModule g.base S.sheaf M)
        (_ : ∀ {M N} (a : M ⟶ N),
          I.map a = eqToHom (hI M) ≫
            TopCat.Sheaf.inverseImageModuleMap g.base S.sheaf M a ≫
              eqToHom (hI N).symm)
        (_ : I.Additive),
        PreservesFiniteLimits I ∧ PreservesFiniteColimits I ∧
        (∀ {P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
          (s : P ⟶ G), CochainComplex.IsKFlatTensorResolution (R := S.sheaf) s →
            CochainComplex.IsKFlatTensorResolution
              (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf)
              ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
        ∃ (E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings T.toRingedSpace))
          (h : ∀ M, E.obj M = Scheme.Modules.tensorPullbackObj g M)
          (_ : ∀ {M N} (a : M ⟶ N),
            E.map a = eqToHom (h M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
              eqToHom (h N).symm)
          (_ : E.Additive)
          (ε : DerivedCategory.Qh ⋙ derivedPullback.{u, w} g ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          (derivedPullback g).IsLeftDerivedFunctor ε
              (HomotopyCategory.quasiIso
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
            (∃ (_ : (derivedPullback g).CommShift ℤ), (derivedPullback g).IsTriangulated) ∧
            ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ,
              CochainComplex.IsKFlatTensor (R := S.sheaf) P →
                IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres, E, hE, hEmap, hEadd, ε, hL, ⟨_, _⟩, hK⟩ :=
    Classical.choose_spec (exists_derivedPullback.{u, w} g)
  have hE' : E = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hE (fun _ _ a ↦ hEmap a)
  subst hE'
  obtain ⟨ρ⟩ := nonempty_tensorPullbackIsoPullback g
  have : (Scheme.Modules.tensorPullback g).Additive := Functor.additive_of_iso ρ.symm
  let ρK : pullbackHomotopyCategory g ≅
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory ρ.inv _
      inv := NatTrans.mapHomotopyCategory ρ.hom _
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, ρ.inv_hom_id, NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, ρ.hom_inv_id, NatTrans.mapHomotopyCategory_id] }
  let τ : (pullbackHomotopyCategory g ⋙ modulesQh T) ⋙
      (schemeDerivedCategoryEquiv.{w} T).inverse ≅
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (modulesQhCompSchemeDerivedCategoryEquivInverse T) ≪≫
      Functor.isoWhiskerRight ρK _
  let φ : derivedPullback.{u, w} g ≅ Classical.choose (exists_derivedPullback.{u, w} g) :=
    Functor.leftDerivedNatIso _ _ (derivedPullbackCounit g) ε
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings S.toRingedSpace))
        (ComplexShape.up ℤ)) τ
  let := Functor.CommShift.ofIso φ.symm ℤ
  have := Functor.CommShift.ofIso_compatibility φ.symm ℤ
  refine ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres, _, hE, hEmap, hEadd,
    Functor.whiskerLeft _ φ.hom ≫ ε, ?_, ⟨inferInstance, Functor.isTriangulated_of_iso φ.symm⟩,
    fun P hP ↦ ?_⟩
  · exact (Functor.isLeftDerivedFunctor_iff_of_iso (α := Functor.whiskerLeft _ φ.hom ≫ ε)
      (α' := ε) (e := φ) (comm := rfl) ..).2 hL
  · have := hK P hP
    dsimp
    infer_instance

end

end AlgebraicGeometry
