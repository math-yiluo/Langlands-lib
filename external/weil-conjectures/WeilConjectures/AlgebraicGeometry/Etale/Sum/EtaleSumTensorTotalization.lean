/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory

/-!
# Étale sum extension and unbounded tensor totalization

Source: literature/stacks-project/more-etale.tex, Tag 0GKF
(blueprint: lem-pur-etale-sum-tensor-totalization).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

namespace AlgebraicGeometry

universe vC vD uC uD

section GenericHomotopies

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Preadditive C] [Preadditive D]
  (F : C ⥤ C ⥤ C) (G : D ⥤ D ⥤ D)
  [F.Additive] [∀ M : C, (F.obj M).Additive]
  [G.Additive] [∀ M : D, (G.obj M).Additive]
  [∀ P H : CochainComplex C ℤ, HomologicalComplex.HasMapBifunctor P H F (.up ℤ)]
  [∀ P H : CochainComplex D ℤ, HomologicalComplex.HasMapBifunctor P H G (.up ℤ)]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]

/-- Comparison families for additive functors and total tensor bifunctors.
Source: literature/stacks-project/homology.tex, Tag 012Z, with more-etale.tex Tag 0GKF;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
def TotalTensorComparison :=
  ∀ (P : CochainComplex C ℤ) (H : CochainComplex D ℤ),
    HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P) H G (.up ℤ) ≅
      (L.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ))

/-- Naturality of a comparison in both chain-map variables.
Source: literature/stacks-project/more-etale.tex, Tag 0GKF, natural projection;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
def TotalTensorNaturality (Ψ : TotalTensorComparison F G L R) : Prop :=
  ∀ (P P' : CochainComplex C ℤ) (H H' : CochainComplex D ℤ)
    (f : P ⟶ P') (g : H ⟶ H'),
    HomologicalComplex.mapBifunctorMap ((L.mapHomologicalComplex (.up ℤ)).map f)
      g G (.up ℤ) ≫ (Ψ P' H').hom =
      (Ψ P H).hom ≫ (L.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f
          ((R.mapHomologicalComplex (.up ℤ)).map g) F (.up ℤ))

/-- The comparison has the prescribed canonical component on every total summand.
Source: literature/stacks-project/homology.tex, Tag 012Z, coproduct terms;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
def TotalTensorSummandNormalization (Ψ : TotalTensorComparison F G L R)
    (a : ∀ (M : C) (N : D),
      (G.obj (L.obj M)).obj N ⟶ L.obj ((F.obj M).obj (R.obj N))) : Prop :=
  ∀ (P : CochainComplex C ℤ) (H : CochainComplex D ℤ)
    (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ) p q n h ≫ (Ψ P H).hom.f n =
        a (P.X p) (H.X q) ≫ L.map
          (HomologicalComplex.ιMapBifunctor P ((R.mapHomologicalComplex (.up ℤ)).obj H)
            F (.up ℤ) p q n h)

/-- The induced bifunctor `K(C) × K(D) ⥤ K(D)`, `(P,H) ↦ Tot(L P ⊗ H)`, on homotopy categories.
Source: literature/stacks-project/homology.tex, Section 010V, maps modulo homotopy;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyLeft :
    (HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory D (.up ℤ) ⥤ HomotopyCategory D (.up ℤ)) :=
  (((whiskeringLeft₂ _).obj (L.mapHomotopyCategory (.up ℤ))).obj
    (𝟭 (HomotopyCategory D (.up ℤ)))).obj
    (G.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))

/-- The induced bifunctor `K(C) × K(D) ⥤ K(D)`, `(P,H) ↦ L Tot(P ⊗ R H)`, on homotopy categories.
Source: literature/stacks-project/homology.tex, Section 010V, maps modulo homotopy;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyRight :
    (HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory D (.up ℤ) ⥤ HomotopyCategory D (.up ℤ)) :=
  ((CategoryTheory.Functor.postcompose₂.obj (L.mapHomotopyCategory (.up ℤ))).obj
    ((((whiskeringLeft₂ _).obj (𝟭 (HomotopyCategory C (.up ℤ)))).obj
      (R.mapHomotopyCategory (.up ℤ))).obj
      (F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))))

/-- Descent is a natural isomorphism between the actual induced bifunctors on
homotopy categories; its components on quotient objects are precisely `Q(Ψ)`.
Source: literature/stacks-project/homology.tex, Section 010V, maps modulo homotopy;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
noncomputable def TotalTensorHomotopyIso
    (Ψ : TotalTensorComparison F G L R) : Prop :=
  ∃ η : TotalTensorHomotopyLeft G L ≅ TotalTensorHomotopyRight F L R,
    ∀ (P : CochainComplex C ℤ) (H : CochainComplex D ℤ),
      ((η.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P)).app
        ((HomotopyCategory.quotient D (.up ℤ)).obj H)) =
          (HomotopyCategory.quotient D (.up ℤ)).map (Ψ P H).hom

private noncomputable def totalTensorMapX
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n : ℤ) :
    (HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ)).X n ⟶
      L.obj ((HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun p q h ↦
    (a (P.X p) (H.X q)).hom ≫ L.map
      (HomologicalComplex.ιMapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n h))

private theorem totalTensorMapX_ι
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ) p q n h ≫ totalTensorMapX F G L R a P H n =
      (a (P.X p) (H.X q)).hom ≫ L.map
        (HomologicalComplex.ιMapBifunctor P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n h) :=
  HomologicalComplex.ι_mapBifunctorDesc _ _ _ _

private theorem totalTensorMapX_orZero
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (p q n : ℤ) :
    HomologicalComplex.ιMapBifunctorOrZero ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ) p q n ≫ totalTensorMapX F G L R a P H n =
      (a (P.X p) (H.X q)).hom ≫ L.map
        (HomologicalComplex.ιMapBifunctorOrZero P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n) := by
  by_cases h : p + q = n
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq _ _ G (.up ℤ) p q n h,
      HomologicalComplex.ιMapBifunctorOrZero_eq _ _ F (.up ℤ) p q n h]
    exact totalTensorMapX_ι F G L R a P H p q n h
  · rw [HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ G (.up ℤ) p q n h,
      HomologicalComplex.ιMapBifunctorOrZero_eq_zero _ _ F (.up ℤ) p q n h]
    simp

private noncomputable def totalTensorInvX
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n : ℤ) :
    L.obj ((HomologicalComplex.mapBifunctor P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)).X n) ⟶
    (HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ)).X n :=
  Cofan.IsColimit.desc
    (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := L) (F := F) P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) n)
    (fun x ↦ (a (P.X x.1.1) (H.X x.1.2)).inv ≫
      HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        H G (.up ℤ) x.1.1 x.1.2 n x.2)

private theorem totalTensorInvX_ι
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (p q n : ℤ) (h : p + q = n) :
    L.map (HomologicalComplex.ιMapBifunctor P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p q n h) ≫
        totalTensorInvX F G L R a P H n =
      (a (P.X p) (H.X q)).inv ≫
        HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
          H G (.up ℤ) p q n h := by
  exact Cofan.IsColimit.fac
    (HomologicalComplex.mapBifunctor.isColimitMapCofan (G := L) (F := F) P
      ((R.mapHomologicalComplex (.up ℤ)).obj H) n)
    (fun x ↦ (a (P.X x.1.1) (H.X x.1.2)).inv ≫
      HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        H G (.up ℤ) x.1.1 x.1.2 n x.2) ⟨⟨p, q⟩, h⟩

private theorem totalTensorMapX_isIso
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n : ℤ) :
    IsIso (totalTensorMapX F G L R a P H n) := by
  refine ⟨totalTensorInvX F G L R a P H n, ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [← Category.assoc, totalTensorMapX_ι, Category.assoc,
      totalTensorInvX_ι, Iso.hom_inv_id_assoc, Category.comp_id]
  · apply HomologicalComplex.mapBifunctor.hom_ext_of_map L
    intro p q hpq
    rw [← Category.assoc, totalTensorInvX_ι, Category.assoc,
      totalTensorMapX_ι, Iso.inv_hom_id_assoc, Category.comp_id]

private theorem totalTensorMapX_comm
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (ha : ∀ {M M' : C} {N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ (a M' N').hom =
        (a M N).hom ≫ L.map
          ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g)))
    (P : CochainComplex C ℤ) (H : CochainComplex D ℤ) (n m : ℤ) :
    (HomologicalComplex.mapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
      H G (.up ℤ)).d n m ≫ totalTensorMapX F G L R a P H m =
    totalTensorMapX F G L R a P H n ≫ L.map
      ((HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)).d n m) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂, Preadditive.add_comp,
    ← Category.assoc _ (totalTensorMapX F G L R a P H n),
    totalTensorMapX_ι F G L R a P H p q n hpq,
    Category.assoc, ← CategoryTheory.Functor.map_comp,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    CategoryTheory.Functor.map_add, Preadditive.comp_add]
  congr 1
  · rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ (by rfl),
      HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _ (by rfl),
      Linear.units_smul_comp, Category.assoc, totalTensorMapX_orZero]
    convert congrArg (fun z ↦
      (ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q)) •
        (z ≫ L.map (HomologicalComplex.ιMapBifunctorOrZero P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) (p + 1) q m)))
        (ha (P.d p (p + 1)) (𝟙 (H.X q))) using 1 <;>
      simp [Units.smul_def, CategoryTheory.Functor.map_comp, Category.assoc]
  · rw [HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ (by rfl),
      HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ _ (by rfl),
      Linear.units_smul_comp, Category.assoc, totalTensorMapX_orZero]
    convert congrArg (fun z ↦
      (ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q)) •
        (z ≫ L.map (HomologicalComplex.ιMapBifunctorOrZero P
          ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ) p (q + 1) m)))
        (ha (𝟙 (P.X p)) (H.d q (q + 1))) using 1 <;>
      simp [Units.smul_def, CategoryTheory.Functor.map_comp, Category.assoc]

private noncomputable def totalTensorIso
    [PreservesColimitsOfSize.{0, 0} L]
    (a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)))
    (ha : ∀ {M M' : C} {N N' : D} (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ (a M' N').hom =
        (a M N).hom ≫ L.map
          ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g))) :
    TotalTensorComparison F G L R := by
  intro P H
  let f : HomologicalComplex.mapBifunctor
      ((L.mapHomologicalComplex (.up ℤ)).obj P) H G (.up ℤ) ⟶
      (L.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.mapBifunctor P
        ((R.mapHomologicalComplex (.up ℤ)).obj H) F (.up ℤ)) :=
    { f := totalTensorMapX F G L R a P H
      comm' n m _ := (totalTensorMapX_comm F G L R a ha P H n m).symm }
  have (n : ℤ) : IsIso (f.f n) := totalTensorMapX_isIso F G L R a P H n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

end GenericHomotopies

/-- The category of sheaves of `A`-modules on the small étale site.
Source: literature/stacks-project/sites-cohomology.tex, Section 06YL;
(blueprint: lem-pur-etale-sum-tensor-totalization). -/
abbrev EtaleModuleSheaf (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)

/-- Unbounded étale sum extension has a total-tensor projection comparison
without quasi-compactness. Source: Stacks Tag 0GKF
(blueprint: lem-coef-etale-open-total-tensor).

Proof: the canonical sheaf projection isomorphism is natural in both factors.
On the summand (p,q), use its inverse, then the canonical inclusion into
j-shriek of the direct-sum total tensor. The left adjoint preserves coproducts,
so each degree map is an isomorphism. Naturality for the two differentials and
additivity preserve their common sign (-1)^p, giving a chain map; the degreewise
inverses give its inverse. The generic totalTensorIso is exactly this construction.
No quasi-compactness, boundedness, flatness or homotopy hypothesis is used. -/
theorem etale_sum_tensor_comparison
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (u : U ⟶ X) (hu : Etale u)
    [IsSeparated u] [LocallyOfFiniteType u] :
    Nonempty (TotalTensorComparison
      (curriedTensor (EtaleModuleSheaf U A)) (curriedTensor (EtaleModuleSheaf X A))
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu)
      (Etale.upperStar (ModuleCat.{u + 1} A) u)) := by
  let L := Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u hu
  let R := Etale.upperStar (ModuleCat.{u + 1} A) u
  let F := curriedTensor (EtaleModuleSheaf U A)
  let G := curriedTensor (EtaleModuleSheaf X A)
  have : PreservesColimitsOfSize.{0, 0} L :=
    (Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) u hu).leftAdjoint_preservesColimits
  let a : ∀ M N, (G.obj (L.obj M)).obj N ≅ L.obj ((F.obj M).obj (R.obj N)) :=
    fun M N ↦ (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu M N).symm
  have ha : ∀ {M M' : EtaleModuleSheaf U A} {N N' : EtaleModuleSheaf X A}
      (f : M ⟶ M') (g : N ⟶ N'),
      (G.map (L.map f)).app N ≫ (G.obj (L.obj M')).map g ≫ (a M' N').hom =
        (a M N).hom ≫ L.map
          ((F.map f).app (R.obj N) ≫ (F.obj M').map (R.map g)) := by
    intro M M' N N' f g
    change (L.map f ⊗ₘ g) ≫
      (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu M' N').inv =
      (Etale.etaleLowerShriekTensorIso (ModuleCat.{u + 1} A) hu M N).inv ≫
        L.map (f ⊗ₘ R.map g)
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (Etale.etaleLowerShriekTensorIso_hom_naturality
      (ModuleCat.{u + 1} A) hu f g).symm
  exact ⟨totalTensorIso F G L R a ha⟩

end AlgebraicGeometry
