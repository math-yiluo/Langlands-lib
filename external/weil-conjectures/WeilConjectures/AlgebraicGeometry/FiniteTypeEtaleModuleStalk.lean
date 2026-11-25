/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Finite generation of geometric stalks of finite type module sheaves

Source: Stacks Project, Tags 03DL (5), 03DE (4), (5), compared with 01B8 and 093N;
the geometric-stalk argument is agent-formulated.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

-- Local surjectivity of the composite lifts the entire coefficient vector at once.
private theorem germ_constant_epi_surjective {Y : Scheme.{u}} {Λ : Type (u + 1)}
    [CommRing Λ] (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (U : Y.Etale) (a : (pointSmallEtale y).fiber.obj U) (M : ModuleCat.{u + 1} Λ)
    (π : (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M ⟶
      G.over U) [Epi π] :
    Function.Surjective
      (((toSheafify (Y.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).app
        (op (Over.mk (𝟙 U)))) ≫ π.hom.app (op (Over.mk (𝟙 U))) ≫
          (pointSmallEtale y).toPresheafFiber U a G.obj) := by
  classical
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := pointSmallEtale y
  let ψ := Φ.over a
  let η := toSheafify (Y.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)
  have : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{u + 1} Λ) π).2 inferInstance
  have : Presheaf.IsLocallySurjective (Y.smallEtaleTopology.over U) π.hom := inferInstance
  have : Presheaf.IsLocallySurjective (Y.smallEtaleTopology.over U) (η ≫ π.hom) :=
    inferInstance
  intro z
  obtain ⟨V, b, t, ht⟩ := Φ.toPresheafFiber_jointly_surjective z
  obtain ⟨W, f, g, _⟩ := IsCofilteredOrEmpty.cone_objs
    (Functor.elementsMk Φ.fiber V b) (Functor.elementsMk Φ.fiber U a)
  let T : Over U := Over.mk g.1
  let c : ψ.fiber.obj T := ⟨W.2, by
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff]
    exact g.2⟩
  let t' : (G.over U).obj.obj (op T) := G.obj.map f.1.op t
  obtain ⟨R, r, ⟨m, hm⟩, d, hd⟩ := ψ.jointly_surjective
    (Presheaf.imageSieve (η ≫ π.hom) t')
    (Presheaf.imageSieve_mem (Y.smallEtaleTopology.over U) (η ≫ π.hom) t') c
  refine ⟨m, ?_⟩
  have hda : Φ.fiber.map R.hom d.1 = a := by
    exact (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 d.2
  have hdr : Φ.fiber.map r.left d.1 = W.2 := congr_arg Subtype.val hd
  have hn := NatTrans.naturality_apply (η ≫ π.hom)
    (Over.homMk R.hom : R ⟶ Over.mk (𝟙 U)).op m
  dsimp at hn
  change Φ.toPresheafFiber U a G.obj ((η ≫ π.hom).app (op (Over.mk (𝟙 U))) m) = z
  calc
    _ = Φ.toPresheafFiber R.left d.1 G.obj
        (G.obj.map R.hom.op ((η ≫ π.hom).app (op (Over.mk (𝟙 U))) m)) := by
      exact (congr_arg (fun e ↦ Φ.toPresheafFiber U e G.obj
        ((η ≫ π.hom).app (op (Over.mk (𝟙 U))) m)) hda).symm.trans
          (ConcreteCategory.congr_hom (Φ.toPresheafFiber_w R.hom d.1 G.obj) _).symm
    _ = Φ.toPresheafFiber R.left d.1 G.obj ((η ≫ π.hom).app (op R) m) := by
      exact congr_arg (Φ.toPresheafFiber R.left d.1 G.obj) hn.symm
    _ = Φ.toPresheafFiber R.left d.1 G.obj (G.obj.map r.left.op t') := by
      exact congr_arg (Φ.toPresheafFiber R.left d.1 G.obj) hm
    _ = Φ.toPresheafFiber W.1 W.2 G.obj t' := by
      exact (ConcreteCategory.congr_hom
        (Φ.toPresheafFiber_w r.left d.1 G.obj) t').trans
          (congr_arg (fun e ↦ Φ.toPresheafFiber W.1 e G.obj t') hdr)
    _ = Φ.toPresheafFiber V b G.obj t := by
      exact (ConcreteCategory.congr_hom
        (Φ.toPresheafFiber_w f.1 W.2 G.obj) t).trans
          (congr_arg (fun e ↦ Φ.toPresheafFiber V e G.obj t) f.2)
    _ = z := ht

private theorem germ_constant_epi_span {Y : Scheme.{u}} {Λ : Type (u + 1)}
    [CommRing Λ] (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (U : Y.Etale) (a : (pointSmallEtale y).fiber.obj U) (n : ℕ)
        (π : (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (Fin n → Λ)) ⟶ G.over U) [Epi π] :
    Submodule.span Λ
      (M := ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G)
      (Set.range fun j : Fin n ↦
        ((pointSmallEtale y).toPresheafFiber U a G.obj).hom
          ((π.hom.app (op (Over.mk (𝟙 U)))).hom
            (((toSheafify (Y.smallEtaleTopology.over U)
              ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ (Fin n → Λ)))).app
                (op (Over.mk (𝟙 U)))).hom (Pi.single j 1)))) = ⊤ := by
  classical
  let L := ((toSheafify (Y.smallEtaleTopology.over U)
    ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ (Fin n → Λ)))).app
      (op (Over.mk (𝟙 U)))) ≫ π.hom.app (op (Over.mk (𝟙 U))) ≫
        (pointSmallEtale y).toPresheafFiber U a G.obj
  change Submodule.span Λ (Set.range fun j : Fin n ↦ L.hom (Pi.single j 1)) = ⊤
  apply top_unique
  intro z _
  obtain ⟨c, rfl⟩ := germ_constant_epi_surjective G Ω y U a _ π z
  change L.hom c ∈ Submodule.span Λ (Set.range fun j : Fin n ↦ L.hom (Pi.single j 1))
  have hc : c = ∑ j : Fin n, c j • Pi.single j (1 : Λ) := by
    apply funext
    intro j
    simp [Pi.single_apply]
  rw [hc, map_sum]
  apply Submodule.sum_mem
  intro j _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))

/-- The geometric stalk of a finite type etale sheaf of `Λ`-modules is a finitely generated
`Λ`-module. More precisely, if on an etale `U → Y` the restriction `G|_U` is generated by
`s_1, ..., s_n ∈ G(U)` (an epimorphism `π` from the constant sheaf of `Λ^n` on the localised
site, `s_j` being the image of the `j`-th basis section), and `a` is a lift of the geometric
point to `U`, then the stalk is generated by the germs of `s_1, ..., s_n` at `(U, a)`.

Source: Stacks Project, Tags 03DL (5), 03DE (4), (5); compare 01B8 and 093N.

Proof (the node's seven steps):
1. Write the stalk as the filtered colimit of sections on pointed neighbourhoods
   (`def-weil-pbc-geometric-stalks`, `definition-torsion-sheaves--3`);
   `lem-weil-pbc-filtered-colimit-modules-elementwise` gives the scalar action on germs.
2. Lift the geometric point to a member of a finite-type generating cover, using
   `definition-torsion-sheaves--3`. The precise assertion implies
   finite generation (`def-weil-finitely-generated-module`).
3. Represent a stalk element on a neighbourhood V and replace V by V times U over Y.
   Cofilteredness and `lem-weil-pbc-etale-scheme-base-change` give a representative over U.
4. The generator epimorphism is locally surjective on underlying abelian sheaves by
   `situation-conventions` and
   `lem-weil-pbc-abelian-sheaf-epi-locally-surjective`. Locally the representative is a
   linear combination of the given sections with coefficients in the constant ring sheaf.
5. Lift the geometric point to one member of that covering using
   `definition-torsion-sheaves--3`.
6. Successively make each of the finitely many coefficients constant on a further pointed
   neighbourhood, using `lem-weil-pbc-constant-ring-sheaf-sections-locally-constant` and the
   same geometric-point lifting lemma. Previously constant coefficients stay constant.
7. Take germs of this equality and use their compatibility with restriction and scalars.
   Every stalk element is a `Λ`-linear combination of the specified germs.
   An empty generating family gives the zero stalk. -/
theorem finite_geometric_stalk_of_isFiniteType {Y : Scheme.{u}} {Λ : Type (u + 1)}
    [CommRing Λ] (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsFiniteTypeEtaleModuleSheaf G)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Module.Finite Λ (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) ∧
      ∀ (U : Y.Etale) (a : (pointSmallEtale y).fiber.obj U) (n : ℕ)
        (π : (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ)) ⟶ G.over U) [Epi π],
        Submodule.span Λ
          (M := ((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G)
          (Set.range fun j : Fin n ↦
            ((pointSmallEtale y).toPresheafFiber U a G.obj).hom
              ((π.hom.app (op (Over.mk (𝟙 U)))).hom
                (((toSheafify (Y.smallEtaleTopology.over U)
                  ((Functor.const (Over U)ᵒᵖ).obj (ModuleCat.of Λ (Fin n → Λ)))).app
                    (op (Over.mk (𝟙 U)))).hom (Pi.single j 1)))) = ⊤ := by
  classical
  have hgen := germ_constant_epi_span G Ω y
  refine ⟨?_, hgen⟩
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨𝒰, h𝒰⟩ := hG
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (y default)
  obtain ⟨a, ha, _⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) y x hx
  obtain ⟨n, π, hπ⟩ := h𝒰 i
  have : Epi π := hπ
  let b : (pointSmallEtale y).fiber.obj (𝒰.etalePrecoverageToEtale i) :=
    Over.homMk a ha
  exact ⟨Submodule.fg_iff_exists_fin_generating_family.mpr
    ⟨n, _, hgen (𝒰.etalePrecoverageToEtale i) b n π⟩⟩

end AlgebraicGeometry.Scheme
