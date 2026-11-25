/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemOrdinaryCokernel
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemAcyclicResolution

/-! # The unit triangle for reduction by a variable positive prime power -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] HasDerivedCategory.standard

private theorem resolution_triangle
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    {X Y Z : DerivedCategory C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e₁ : DerivedCategory.Q.obj S.X₁ ≅ X)
    (e₂ : DerivedCategory.Q.obj S.X₂ ≅ Y)
    (e₃ : DerivedCategory.Q.obj S.X₃ ≅ Z)
    (hf : DerivedCategory.Q.map S.f ≫ e₂.hom = e₁.hom ≫ f)
    (hg : DerivedCategory.Q.map S.g ≫ e₃.hom = e₂.hom ≫ g) :
    ∃ δ, Triangle.mk f g δ ∈ distTriang (DerivedCategory C) := by
  let V := DerivedCategory.triangleOfSES hS
  let δ := e₃.inv ≫ V.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
  let W := Triangle.mk f g δ
  let eV : V ≅ W := Triangle.isoMk V W e₁ e₂ e₃ hf hg (by
    change V.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' =
      e₃.hom ≫ e₃.inv ≫ V.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
    simp only [Iso.hom_inv_id_assoc]
    rfl)
  exact ⟨δ, isomorphic_distinguished V (DerivedCategory.triangleOfSES_distinguished hS)
    W eV.symm⟩

private theorem power_triangle_assembly
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    {E : C ⥤ D} {R : D ⥤ C}
    [E.Additive] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (r : DerivedExtension E R) (V : C ⥤ C) [V.Additive] (mu : V ⟶ 𝟭 C) (X : C)
    (hquot : ∀ Y : C,
      ∃ hz : mu.app Y ≫ r.adjunction.unit.app Y = 0,
        Nonempty (IsColimit (CokernelCofork.ofπ (r.adjunction.unit.app Y) hz)))
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (P : CochainComplex C ℤ) (q : P ⟶ K),
        QuasiIso q ∧ (∀ i : ℤ, Mono (mu.app (P.X i))) ∧
        QuasiIso ((V.mapHomologicalComplex (.up ℤ)).map q) ∧
        IsIso (r.epsilon.app P)) :
    ∃ δ, Triangle.mk ((DerivedCategory.singleFunctor C 0).map (mu.app X))
      (r.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor C 0).obj X))
      δ ∈ distTriang (DerivedCategory C) := by
  classical
  let K := (CochainComplex.singleFunctor C 0).obj X
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let muc := NatTrans.mapHomologicalComplex mu (.up ℤ)
  obtain ⟨P, q, hq, hm, hqv, heps⟩ := hres K
  let : QuasiIso q := hq
  have hqq : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C q).2 hq
  let : IsIso (r.epsilon.app P) := heps
  let a := r.adjunction
  let ad := r.derivedAdjunction
  let L := r.derived
  let uc := (a.mapHomologicalComplex (.up ℤ)).unit.app P
  have hz : muc.app P ≫ uc = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact (hquot (P.X i)).choose
  have hS : (ShortComplex.mk (muc.app P) uc hz).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro i
    obtain ⟨hi, ⟨hc⟩⟩ := hquot (P.X i)
    have hmono : Mono (mu.app (P.X i)) := hm i
    have hepi : Epi (a.unit.app (P.X i)) := Cofork.IsColimit.epi hc
    have hs : (ShortComplex.mk (mu.app (P.X i)) (a.unit.app (P.X i)) hi).ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ hc }
    exact hs
  let := hqv
  let ev := (HomologicalComplex.singleMapHomologicalComplex V (.up ℤ) 0).app X
  let eK : Vc.obj K ≅ (CochainComplex.singleFunctor C 0).obj (V.obj X) := ev
  let e₁ : DerivedCategory.Q.obj (Vc.obj P) ≅
      (DerivedCategory.singleFunctor C 0).obj (V.obj X) :=
    asIso (DerivedCategory.Q.map (Vc.map q)) ≪≫ DerivedCategory.Q.mapIso eK
  let e₂ : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor C 0).obj X :=
    @asIso (DerivedCategory C) _ _ _ (DerivedCategory.Q.map q) hqq
  let e₃ : DerivedCategory.Q.obj
      ((R.mapHomologicalComplex (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≅
      R.mapDerivedCategory.obj (L.obj ((DerivedCategory.singleFunctor C 0).obj X)) :=
    (R.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      R.mapDerivedCategory.mapIso (asIso (r.epsilon.app P)).symm ≪≫
      R.mapDerivedCategory.mapIso (L.mapIso e₂)
  have hnormal : ad.unit.app (DerivedCategory.Q.obj P) ≫
      R.mapDerivedCategory.map (r.epsilon.app P) ≫
      R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map uc := by
    have ht := r.transpose P ((E.mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
    simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id] at ht
    erw [Category.comp_id, Category.comp_id] at ht
    simpa only [Category.assoc] using ht
  have hg : DerivedCategory.Q.map uc ≫ e₃.hom =
      e₂.hom ≫ ad.unit.app ((DerivedCategory.singleFunctor C 0).obj X) := by
    change DerivedCategory.Q.map uc ≫
      R.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      R.mapDerivedCategory.map (inv (r.epsilon.app P)) ≫
      R.mapDerivedCategory.map (L.map e₂.hom) = _
    erw [← hnormal]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← R.mapDerivedCategory.map_comp_assoc, IsIso.hom_inv_id]
    simp only [R.mapDerivedCategory.map_id, Category.id_comp]
    exact (ad.unit.naturality e₂.hom).symm
  have hfirst : muc.app K =
      eK.hom ≫ (CochainComplex.singleFunctor C 0).map (mu.app X) := by
    apply HomologicalComplex.to_single_hom_ext
    change mu.app (K.X 0) = eK.hom.f 0 ≫
      ((CochainComplex.singleFunctor C 0).map (mu.app X)).f 0
    dsimp only [eK, ev]
    erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self]
    erw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, mu.naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hf : DerivedCategory.Q.map (muc.app P) ≫ e₂.hom =
      e₁.hom ≫ (DerivedCategory.singleFunctor C 0).map (mu.app X) := by
    change DerivedCategory.Q.map (muc.app P) ≫ DerivedCategory.Q.map q = _
    erw [← CategoryTheory.Functor.map_comp]
    have hn := (muc.naturality q).symm
    change muc.app P ≫ q = Vc.map q ≫ muc.app K at hn
    erw [hn, hfirst, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    erw [← Category.assoc]
    rfl
  exact resolution_triangle hS ((DerivedCategory.singleFunctor C 0).map (mu.app X))
    (ad.unit.app ((DerivedCategory.singleFunctor C 0).obj X)) e₁ e₂ e₃ hf hg

/-- Reduction of the constant units tower has the power-system multiplication triangle.
No invertibility of the prime on the scheme or surjectivity of the power map is assumed.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
and the coefficient-resolution calculation in step 1 of lem-sfb-kummer-reduction-unit.
(blueprint: lem-sfb-power-system-reduction-triangle).

Proof: work on the sequence site. The quotient coefficient system has the bounded flat
integer resolution [Z --l^(n+1)--> Z], in degrees -1 and 0, whose transition is
multiplication by l in degree -1 and the identity in degree 0. Tensor a flat-term
K-flat resolution of the constant units system with this resolution. The resulting
short exact sequence of total complexes has first map multiplication by l^(n+1)
at level n and has quotient the ordinary scalar extension of that K-flat resolution.
The two integer terms identify respectively with the power-transition and constant
units systems. The flat resolution of the coefficient system identifies the quotient
with the restriction of derived extension. This gives the asserted distinguished
triangle, including its map from units. For an arbitrary supplied reduction, uniqueness
of ordinary left adjoints identifies its ordinary functor with sheafified extension,
compatibly with the ordinary unit. Uniqueness of universal derived pairs identifies
its derived functor and counit with the K-flat model. Apply the representative
transpose equation to its counit to identify the map from units with its actual
adjunction unit. Transporting the distinguished triangle along these isomorphisms
gives the assertion. The component prescription determines p as a natural
transformation, so the first map is precisely the supplied p. All constructions
are on the sequence site before evaluation. This argument uses no Kummer exactness;
when the prime is not invertible, degree-zero cohomology need not vanish. -/
theorem powerSystem_reduction_triangle (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (p : powerUnits l T ⟶ units T)
    (hp : ∀ n : ℕ, p.app (op n) = Scheme.proEtaleUnitsPower T (l ^ (n + 1))) :
    ∃ δ, Triangle.mk ((DerivedCategory.singleFunctor (Ab T) 0).map p)
      (r.derivedAdjunction.unit.app ((DerivedCategory.singleFunctor (Ab T) 0).obj (units T)))
      δ ∈ distTriang (DerivedCategory (Ab T)) := by
  let V := PowerTransition.functor (C := DiagonalAb T) l
  let mu := PowerTransition.multiplication (C := DiagonalAb T) l
  have hres : ∀ K : CochainComplex (Ab T) ℤ,
      ∃ (P : CochainComplex (Ab T) ℤ) (q : P ⟶ K),
        QuasiIso q ∧ (∀ i : ℤ, Mono (mu.app (P.X i))) ∧
        QuasiIso ((V.mapHomologicalComplex (.up ℤ)).map q) ∧
        IsIso (r.model.epsilon.app P) := by
    intro K
    obtain ⟨P, q, hq, hm, heps⟩ := powerSystem_acyclic_resolution l T r K
    let : QuasiIso q := hq
    refine ⟨P, q, hq, ?_, ?_, heps⟩
    · intro i
      exact (NatTrans.mono_iff_mono_app _).2 (fun n ↦ hm i n.unop)
    · exact PowerTransition.quasiIso_map l q
  have h := power_triangle_assembly (C := Ab T) r.model V mu (units T)
    (powerSystem_ordinary_cokernel l T r) hres
  have hp' : mu.app (units T) = p := by
    apply NatTrans.ext
    funext n
    exact (hp n.unop).symm
  rw [hp'] at h
  convert! h using 1

end AlgebraicGeometry.ProEtale.SpTowerClasses
