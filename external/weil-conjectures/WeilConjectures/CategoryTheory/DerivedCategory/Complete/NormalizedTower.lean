/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Strict models of normalized towers

Let `(C, J)` be an essentially small site, `R` a commutative ring and `I` an ideal, and put
`A_n = R ⧸ Iⁿ`. A *normalized tower* is a family of objects `L_n ∈ D(J, A_n)` with transition
maps `t_n : L_{n+1} ⟶ Res L_n` exhibiting `L_n` as the derived base change
`L_{n+1} ⊗ᴸ_{A_{n+1}} A_n` (`CategoryTheory.Sheaf.IsDerivedBaseChange`).

This file shows that a normalized tower is represented by a tower of K-flat complexes and chain
maps: there are K-flat complexes `P_n` of flat sheaves of `A_n`-modules with
`Q P_n ≅ L_n` and chain maps `P_{n+1} ⟶ Res P_n` representing the transition maps
(`DerivedCategory.exists_kFlatModelTower`).

## Main definitions

- `CochainComplex.IsKFlat`: K-flat complexes.
- `DerivedCategory.KFlatModel`: a K-flat model of an object of the derived category.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{v} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜]

/-- A complex `P` is *K-flat* if tensoring with it preserves quasi-isomorphisms. This is
`(HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P`, packaged as a definition so that it can be
stated for concrete categories without searching for the monoidal structure on complexes. -/
def CochainComplex.IsKFlat (P : CochainComplex 𝒜 ℤ) : Prop :=
  (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P

/-- Every complex has a resolution by a K-flat complex of flat objects. -/
lemma CochainComplex.exists_quasiIso_isKFlat (L : CochainComplex 𝒜 ℤ) :
    ∃ (P : CochainComplex 𝒜 ℤ) (π : P ⟶ L), QuasiIso π ∧ (∀ n, ObjectProperty.flat (P.X n)) ∧
      P.IsKFlat :=
  CochainComplex.exists_quasiIso_flat_kFlat L

end

/-- Factoring a map through an exact cokernel presentation and a quasi-isomorphism gives a
quasi-isomorphism from the cokernel. -/
private lemma CochainComplex.quasiIso_cokernelDesc_of_exact_factor
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {X Y Z T : CochainComplex 𝒜 ℤ}
    (f : X ⟶ Y) (ρ : Y ⟶ Z) (w : f ≫ ρ = 0) (hS : (ShortComplex.mk f ρ w).Exact)
    [Epi ρ] (g : Z ⟶ T) [QuasiIso g] (t : Y ⟶ T) (ht : ρ ≫ g = t)
    (wt : f ≫ t = 0) : QuasiIso (cokernel.desc f t wt) := by
  let c := (cokernelIsCokernel f).coconePointUniqueUpToIso hS.gIsCokernel
  have hc : cokernel.π f ≫ c.hom = ρ :=
    (cokernelIsCokernel f).comp_coconePointUniqueUpToIso_hom hS.gIsCokernel
      WalkingParallelPair.one
  have heq : cokernel.desc f t wt = c.hom ≫ g := by
    apply coequalizer.hom_ext
    rw [cokernel.π_desc, reassoc_of% hc, ht]
  rw [heq]
  infer_instance

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

/-- A *K-flat model* of an object `L` of `D(J, A)`: a K-flat complex of flat sheaves of
`A`-modules together with an isomorphism `Q P ≅ L`. -/
structure KFlatModel {A : Type (u + 1)} [CommRing A]
    (L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) where
  /-- The complex. -/
  P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ
  flat (i : ℤ) : ObjectProperty.flat (P.X i)
  isKFlat : P.IsKFlat
  /-- The isomorphism `Q P ≅ L`. -/
  iso : Q.obj P ≅ L

namespace KFlatModel

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']

/-- Every object has a K-flat model. -/
lemma nonempty (L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    Nonempty (KFlatModel L) := by
  obtain ⟨P, π, hπ, hflat, hP⟩ := CochainComplex.exists_quasiIso_isKFlat (Q.objPreimage L)
  have : IsIso (Q.map π) := (isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  exact ⟨⟨P, hflat, hP, asIso (Q.map π) ≪≫ Q.objObjPreimageIso L⟩⟩

/-- A morphism `L' ⟶ Res L` to the restriction of scalars of an object with a K-flat model `M`
is represented by a chain map `P' ⟶ Res P` out of some K-flat model `M'` of `L'`. -/
lemma exists_hom (f : A' →+* A) {L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
    (M : KFlatModel L) {L' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A'))}
    (t : L' ⟶ (Sheaf.derivedRestrictScalars J f).obj L) :
    ∃ (M' : KFlatModel L')
      (g : M'.P ⟶ ((Sheaf.restrictScalars J f).mapHomologicalComplex (.up ℤ)).obj M.P),
      Q.map g ≫ (Sheaf.restrictScalars J f).mapDerivedCategoryFactors.inv.app M.P ≫
          (Sheaf.derivedRestrictScalars J f).map M.iso.hom = M'.iso.hom ≫ t := by
  let F := Sheaf.restrictScalars J f
  let Y := Q.objPreimage L'
  let eY : Q.obj Y ≅ L' := Q.objObjPreimageIso L'
  let φ : Q.obj Y ⟶ Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj M.P) :=
    eY.hom ≫ t ≫ (Sheaf.derivedRestrictScalars J f).map M.iso.inv ≫
      F.mapDerivedCategoryFactors.hom.app M.P
  obtain ⟨X, s, _, g, hφ⟩ := right_fac φ
  obtain ⟨P, π, hπ, hflat, hP⟩ := CochainComplex.exists_quasiIso_isKFlat X
  have : IsIso (Q.map π) := (isIso_Q_map_iff_quasiIso (φ := π)).2 hπ
  refine ⟨⟨P, hflat, hP, asIso (Q.map π) ≪≫ asIso (Q.map s) ≪≫ eY⟩, π ≫ g, ?_⟩
  have hg : Q.map g = Q.map s ≫ φ := by rw [hφ, IsIso.hom_inv_id_assoc]
  simp only [Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc, hg, φ, F]
  simp

end KFlatModel

section Restrict

variable {A A' A'' : Type (u + 1)} [CommRing A] [CommRing A'] [CommRing A'']
  {f : A →+* A'} {g : A' →+* A''} {gf : A →+* A''} (hgf : gf = g.comp f)

/-- On the image of a complex, `Sheaf.derivedRestrictScalarsCompIso` is the image of the
composition isomorphism of restrictions of scalars of complexes. -/
lemma derivedRestrictScalarsCompIso_hom_app_Q_obj
    (K : CochainComplex (Sheaf J (ModuleCat.{u + 1} A'')) ℤ) :
    (Sheaf.restrictScalars J f).mapDerivedCategoryFactors.inv.app
        (((Sheaf.restrictScalars J g).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Sheaf.derivedRestrictScalars J f).map
        ((Sheaf.restrictScalars J g).mapDerivedCategoryFactors.inv.app K) ≫
      (Sheaf.derivedRestrictScalarsCompIso J hgf).hom.app (Q.obj K) =
    Q.map ((Functor.mapHomologicalComplexCompIso
        (Sheaf.restrictScalarsCompIso J f g gf hgf) (.up ℤ)).hom.app K) ≫
      (Sheaf.restrictScalars J gf).mapDerivedCategoryFactors.inv.app K := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac (Sheaf.restrictScalars J g)
    (Sheaf.restrictScalars J f) K
  have h₂ := Functor.mapDerivedCategoryNatIso_fac (Sheaf.restrictScalarsCompIso J f g gf hgf) K
  have h₃ : Q.map ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (Sheaf.restrictScalars J g ⋙ Sheaf.restrictScalars J f)) (.up ℤ)).hom.app K) =
      𝟙 _ := by
    rw [← Q.map_id]
    congr 1
  rw [h₃] at h₁
  erw [Category.comp_id] at h₁
  have e₁ : ((Sheaf.restrictScalars J g).mapDerivedCategoryCompIso
      (Sheaf.restrictScalars J f)).hom.app (Q.obj K) =
      (Sheaf.derivedRestrictScalars J f).map
        ((Sheaf.restrictScalars J g).mapDerivedCategoryFactors.hom.app K) ≫
      (Sheaf.restrictScalars J f).mapDerivedCategoryFactors.hom.app
        (((Sheaf.restrictScalars J g).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Sheaf.restrictScalars J g ⋙ Sheaf.restrictScalars J f).mapDerivedCategoryFactors.inv.app
        K := by
    rw [← cancel_epi (((Sheaf.restrictScalars J g).mapDerivedCategoryCompIso
      (Sheaf.restrictScalars J f)).inv.app (Q.obj K)), Iso.inv_hom_id_app, reassoc_of% h₁,
      Iso.hom_inv_id_app]
    rfl
  have e₂ : (Functor.mapDerivedCategoryNatIso
      (Sheaf.restrictScalarsCompIso J f g gf hgf)).hom.app (Q.obj K) =
      (Sheaf.restrictScalars J g ⋙ Sheaf.restrictScalars J f).mapDerivedCategoryFactors.hom.app
        K ≫ Q.map ((NatTrans.mapHomologicalComplex
          (Sheaf.restrictScalarsCompIso J f g gf hgf).hom (.up ℤ)).app K) ≫
      (Sheaf.restrictScalars J gf).mapDerivedCategoryFactors.inv.app K := by
    rw [← reassoc_of% h₂]
    simp
  simp only [Sheaf.derivedRestrictScalarsCompIso, Iso.trans_hom,
    NatTrans.comp_app, e₁, e₂, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rfl

end Restrict

section Tower

variable {A : ℕ → Type (u + 1)} [∀ n, CommRing (A n)] {φ : ∀ n, A (n + 1) →+* A n}
  (L : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (A n))))
  (t : ∀ n : ℕ, L (n + 1) ⟶ (Sheaf.derivedRestrictScalars J (φ n)).obj (L n))

/-- K-flat models of the levels of a tower, chosen inductively so that the transition maps are
represented by chain maps (`DerivedCategory.towerModelMap`). -/
noncomputable def towerModel (n : ℕ) : KFlatModel (L n) :=
  Nat.rec (motive := fun n ↦ KFlatModel (L n)) (KFlatModel.nonempty (L 0)).some
    (fun n M ↦ (KFlatModel.exists_hom _ M (t n)).choose) n

lemma towerModel_succ (n : ℕ) :
    towerModel L t (n + 1) = (KFlatModel.exists_hom _ (towerModel L t n) (t n)).choose :=
  rfl

/-- The chain maps `P_{n+1} ⟶ Res P_n` representing the transition maps of a tower. -/
noncomputable def towerModelMap (n : ℕ) :
    (towerModel L t (n + 1)).P ⟶ ((Sheaf.restrictScalars J (φ n)).mapHomologicalComplex (.up ℤ)).obj
      (towerModel L t n).P :=
  (KFlatModel.exists_hom _ (towerModel L t n) (t n)).choose_spec.choose

lemma towerModelMap_spec (n : ℕ) :
    Q.map (towerModelMap L t n) ≫ (Sheaf.restrictScalars J (φ n)).mapDerivedCategoryFactors.inv.app
        (towerModel L t n).P ≫
      (Sheaf.derivedRestrictScalars J (φ n)).map (towerModel L t n).iso.hom =
    (towerModel L t (n + 1)).iso.hom ≫ t n :=
  (KFlatModel.exists_hom _ (towerModel L t n) (t n)).choose_spec.choose_spec

end Tower

section Coherence

variable {A₀ A₁ A₂ A₃ : Type (u + 1)} [CommRing A₀] [CommRing A₁] [CommRing A₂] [CommRing A₃]
  (f₁ : A₀ →+* A₁) (f₂ : A₁ →+* A₂) (f₃ : A₂ →+* A₃) (f₁₂ : A₀ →+* A₂) (f₂₃ : A₁ →+* A₃)
  (f₁₂₃ : A₀ →+* A₃) (h₁₂ : f₁₂ = f₂.comp f₁) (h₂₃ : f₂₃ = f₃.comp f₂)
  (h₁ : f₁₂₃ = f₂₃.comp f₁) (h₂ : f₁₂₃ = f₃.comp f₁₂)

omit [EssentiallySmall.{u + 1} C] in
/-- The composition isomorphisms of restrictions of scalars are associative. -/
lemma _root_.CategoryTheory.Sheaf.restrictScalarsCompIso_assoc
    (F : Sheaf J (ModuleCat.{u + 1} A₃)) :
    (Sheaf.restrictScalars J f₁).map ((Sheaf.restrictScalarsCompIso J f₂ f₃ f₂₃ h₂₃).hom.app F) ≫
        (Sheaf.restrictScalarsCompIso J f₁ f₂₃ f₁₂₃ h₁).hom.app F =
      (Sheaf.restrictScalarsCompIso J f₁ f₂ f₁₂ h₁₂).hom.app ((Sheaf.restrictScalars J f₃).obj F) ≫
        (Sheaf.restrictScalarsCompIso J f₁₂ f₃ f₁₂₃ h₂).hom.app F := by
  ext U x
  rfl

omit [EssentiallySmall.{u + 1} C] in
/-- The composition isomorphisms of restrictions of scalars of complexes are associative. -/
lemma restrictScalarsCompIso_assoc_complex
    (K : CochainComplex (Sheaf J (ModuleCat.{u + 1} A₃)) ℤ) :
    ((Sheaf.restrictScalars J f₁).mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J f₂ f₃ f₂₃ h₂₃)
          (.up ℤ)).hom.app K) ≫
        (Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J f₁ f₂₃ f₁₂₃ h₁)
          (.up ℤ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J f₁ f₂ f₁₂ h₁₂)
          (.up ℤ)).hom.app (((Sheaf.restrictScalars J f₃).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J f₁₂ f₃ f₁₂₃ h₂)
          (.up ℤ)).hom.app K := by
  ext i : 1
  exact Sheaf.restrictScalarsCompIso_assoc f₁ f₂ f₃ f₁₂ f₂₃ f₁₂₃ h₁₂ h₂₃ h₁ h₂ (K.X i)

end Coherence

section RTower

variable {R : Type (u + 1)} [CommRing R] {A : ℕ → Type (u + 1)} [∀ n, CommRing (A n)]
  (φ : ∀ {n m : ℕ}, n ≤ m → A m →+* A n) (ψ : ∀ n, R →+* A n)
  (hψ : ∀ {n m : ℕ} (h : n ≤ m), (φ h).comp (ψ m) = ψ n)
  (L : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (A n))))
  (t : ∀ n : ℕ, L (n + 1) ⟶ (Sheaf.derivedRestrictScalars J (φ n.le_succ)).obj (L n))

/-- The levels `Res P_n` of the strict model of a normalized tower, complexes of sheaves of
`R`-modules. -/
noncomputable abbrev towerComplex (n : ℕ) : CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ :=
  ((Sheaf.restrictScalars J (ψ n)).mapHomologicalComplex (.up ℤ)).obj
    (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P

/-- The transition maps of the strict model of a normalized tower. -/
noncomputable def towerComplexMap (n : ℕ) :
    towerComplex φ ψ L t (n + 1) ⟶ towerComplex φ ψ L t n :=
  ((Sheaf.restrictScalars J (ψ (n + 1))).mapHomologicalComplex (.up ℤ)).map
      (towerModelMap (φ := fun n ↦ φ n.le_succ) L t n) ≫
    (Functor.mapHomologicalComplexCompIso
      (Sheaf.restrictScalarsCompIso J (ψ (n + 1)) (φ n.le_succ) (ψ n) (hψ _).symm)
        (.up ℤ)).hom.app _

/-- The strict model of a normalized tower, a tower of complexes of sheaves of `R`-modules. -/
noncomputable def towerFunctor : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ :=
  Functor.ofOpSequence (towerComplexMap φ ψ hψ L t)

/-- The identification of the levels of the strict model with the restrictions of scalars of
the given levels. -/
noncomputable def towerFunctorIso (n : ℕ) :
    Q.obj ((towerFunctor φ ψ hψ L t).obj (op n)) ≅
      (Sheaf.derivedRestrictScalars J (ψ n)).obj (L n) :=
  ((Sheaf.restrictScalars J (ψ n)).mapDerivedCategoryFactors.app _).symm ≪≫
    (Sheaf.derivedRestrictScalars J (ψ n)).mapIso (towerModel (φ := fun n ↦ φ n.le_succ) L t n).iso

/-- The strict model represents the transition maps of the tower. -/
lemma Q_map_towerFunctor_map_comp_towerFunctorIso_hom (n : ℕ) :
    Q.map ((towerFunctor φ ψ hψ L t).map (homOfLE n.le_succ).op) ≫
        (towerFunctorIso φ ψ hψ L t n).hom =
      (towerFunctorIso φ ψ hψ L t (n + 1)).hom ≫
        (Sheaf.derivedRestrictScalars J (ψ (n + 1))).map (t n) ≫
        (Sheaf.derivedRestrictScalarsCompIso J (hψ n.le_succ).symm).hom.app (L n) := by
  have h := towerModelMap_spec (φ := fun n ↦ φ n.le_succ) L t n
  have h' := derivedRestrictScalarsCompIso_hom_app_Q_obj (J := J) (hψ n.le_succ).symm
    (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P
  simp only [towerFunctor, Functor.ofOpSequence_map_homOfLE_succ, towerComplexMap,
    towerFunctorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  have hnat := (Sheaf.derivedRestrictScalarsCompIso J (hψ n.le_succ).symm).hom.naturality
    (towerModel (φ := fun n ↦ φ n.le_succ) L t n).iso.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [← Functor.map_comp_assoc (Sheaf.derivedRestrictScalars J (ψ (n + 1))) _ (t n), ← h]
  simp only [Functor.map_comp, Category.assoc, hnat, Iso.app_inv]
  erw [← Functor.mapDerivedCategoryFactors_inv_naturality_assoc]
  erw [reassoc_of% h']

variable (hφ : ∀ {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k), (φ h₁).comp (φ h₂) = φ (h₁.trans h₂))

/-- The composite chain maps `P_{n+k+1} ⟶ Res P_n` of the strict model of a tower. -/
noncomputable def towerModelComp (n : ℕ) : ∀ k : ℕ,
    (towerModel (φ := fun n ↦ φ n.le_succ) L t (n + k + 1)).P ⟶
      ((Sheaf.restrictScalars J (φ (Nat.le_add_right n (k + 1)))).mapHomologicalComplex
        (.up ℤ)).obj (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P
  | 0 => towerModelMap (φ := fun n ↦ φ n.le_succ) L t n
  | k + 1 => towerModelMap (φ := fun n ↦ φ n.le_succ) L t (n + k + 1) ≫
      ((Sheaf.restrictScalars J (φ (n + k + 1).le_succ)).mapHomologicalComplex (.up ℤ)).map
        (towerModelComp n k) ≫
      (Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J
        (φ (n + k + 1).le_succ) (φ (Nat.le_add_right n (k + 1)))
        (φ (Nat.le_add_right n (k + 2))) (hφ _ _).symm) (.up ℤ)).hom.app _

/-- The chain maps of the strict model represent derived base changes. -/
lemma isDerivedBaseChange_towerModelMap (ht : ∀ n, Sheaf.IsDerivedBaseChange (t n)) (n : ℕ) :
    Sheaf.IsDerivedBaseChange (Q.map (towerModelMap (φ := fun n ↦ φ n.le_succ) L t n) ≫
      (Sheaf.restrictScalars J (φ n.le_succ)).mapDerivedCategoryFactors.inv.app
        (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P) := by
  have h := towerModelMap_spec (φ := fun n ↦ φ n.le_succ) L t n
  have : Q.map (towerModelMap (φ := fun n ↦ φ n.le_succ) L t n) ≫
      (Sheaf.restrictScalars J (φ n.le_succ)).mapDerivedCategoryFactors.inv.app
        (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P =
      (towerModel (φ := fun n ↦ φ n.le_succ) L t (n + 1)).iso.hom ≫ t n ≫
        (Sheaf.derivedRestrictScalars J (φ n.le_succ)).map
          (towerModel (φ := fun n ↦ φ n.le_succ) L t n).iso.inv := by
    rw [← reassoc_of% h, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  rw [this, ← Category.assoc]
  exact ((ht n).of_iso (towerModel (φ := fun n ↦ φ n.le_succ) L t (n + 1)).iso).comp_map_iso
    (towerModel (φ := fun n ↦ φ n.le_succ) L t n).iso.symm

/-- The composite chain maps of the strict model represent derived base changes. -/
lemma isDerivedBaseChange_towerModelComp (ht : ∀ n, Sheaf.IsDerivedBaseChange (t n))
    (n k : ℕ) :
    Sheaf.IsDerivedBaseChange (Q.map (towerModelComp φ L t hφ n k) ≫
      (Sheaf.restrictScalars J (φ (Nat.le_add_right n (k + 1)))).mapDerivedCategoryFactors.inv.app
        (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P) := by
  induction k with
  | zero => exact isDerivedBaseChange_towerModelMap φ L t ht n
  | succ k ih =>
    have h' := derivedRestrictScalarsCompIso_hom_app_Q_obj (J := J)
      (hφ (Nat.le_add_right n (k + 1)) (n + k + 1).le_succ).symm
      (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P
    have := (isDerivedBaseChange_towerModelMap φ L t ht (n + k + 1)).comp
      (hφ (Nat.le_add_right n (k + 1)) (n + k + 1).le_succ).symm ih
    have key : Q.map (towerModelComp φ L t hφ n (k + 1)) ≫
        (Sheaf.restrictScalars J (φ (Nat.le_add_right n (k + 2)))).mapDerivedCategoryFactors.inv.app
          (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P =
        (Q.map (towerModelMap (φ := fun n ↦ φ n.le_succ) L t (n + k + 1)) ≫
          (Sheaf.restrictScalars J (φ (n + k + 1).le_succ)).mapDerivedCategoryFactors.inv.app
            (towerModel (φ := fun n ↦ φ n.le_succ) L t (n + k + 1)).P) ≫
        (Sheaf.derivedRestrictScalars J (φ (n + k + 1).le_succ)).map
          (Q.map (towerModelComp φ L t hφ n k) ≫
            (Sheaf.restrictScalars J
              (φ (Nat.le_add_right n (k + 1)))).mapDerivedCategoryFactors.inv.app
              (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P) ≫
        (Sheaf.derivedRestrictScalarsCompIso J
          (hφ (Nat.le_add_right n (k + 1)) (n + k + 1).le_succ).symm).hom.app
            (Q.obj (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P) := by
      dsimp only [towerModelComp]
      simp only [Functor.map_comp, Category.assoc]
      rw [← h', Functor.mapDerivedCategoryFactors_inv_naturality_assoc]
    rw [key]
    exact this

/-- The transition maps `T_{n+k+1} ⟶ T_n` of the strict model are the restrictions of scalars
of the composite chain maps. -/
lemma towerFunctor_map_homOfLE (n k : ℕ) :
    (towerFunctor φ ψ hψ L t).map (homOfLE (Nat.le_add_right n (k + 1))).op =
      ((Sheaf.restrictScalars J (ψ (n + k + 1))).mapHomologicalComplex (.up ℤ)).map
          (towerModelComp φ L t hφ n k) ≫
        (Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J (ψ (n + k + 1))
          (φ (Nat.le_add_right n (k + 1))) (ψ n) (hψ _).symm) (.up ℤ)).hom.app _ := by
  induction k with
  | zero => exact Functor.ofOpSequence_map_homOfLE_succ _ n
  | succ k ih =>
    have h : (homOfLE (Nat.le_add_right n (k + 2))).op =
        (homOfLE (n + k + 1).le_succ).op ≫ (homOfLE (Nat.le_add_right n (k + 1))).op := rfl
    rw [h, Functor.map_comp, ih]
    erw [Functor.ofOpSequence_map_homOfLE_succ]
    have hnat := (Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J
      (ψ (n + (k + 1) + 1)) (φ (n + k + 1).le_succ) (ψ (n + k + 1)) (hψ _).symm)
        (.up ℤ)).hom.naturality
        (towerModelComp φ L t hφ n k)
    have hcoh := restrictScalarsCompIso_assoc_complex (J := J) (ψ (n + (k + 1) + 1))
      (φ (n + k + 1).le_succ) (φ (Nat.le_add_right n (k + 1))) (ψ (n + k + 1))
      (φ (Nat.le_add_right n (k + 2))) (ψ n) (hψ _).symm (hφ _ _).symm (hψ _).symm (hψ _).symm
      (towerModel (φ := fun n ↦ φ n.le_succ) L t n).P
    simp only [Functor.comp_obj, Functor.comp_map] at hnat
    simp only [towerComplexMap, towerModelComp, Functor.map_comp, Category.assoc]
    rw [hcoh, reassoc_of% hnat]
    rfl

end RTower

section Smul

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (f : A →+* A')

omit [EssentiallySmall.{u + 1} C] in
lemma _root_.CategoryTheory.Sheaf.restrictScalars_map_smul (r : A)
    {F G : Sheaf J (ModuleCat.{u + 1} A')} (g : F ⟶ G) :
    (Sheaf.restrictScalars J f).map (f r • g) = r • (Sheaf.restrictScalars J f).map g := by
  ext U x
  rfl

omit [EssentiallySmall.{u + 1} C] in
lemma _root_.CategoryTheory.Sheaf.smul_id_restrictScalars_obj {r : A} (hr : f r = 0)
    (F : Sheaf J (ModuleCat.{u + 1} A')) :
    r • 𝟙 ((Sheaf.restrictScalars J f).obj F) = 0 := by
  rw [← CategoryTheory.Functor.map_id, ← Sheaf.restrictScalars_map_smul, hr, zero_smul,
    Functor.map_zero]

end Smul

section Normalized

variable {R : Type (u + 1)} [CommRing R] {A : ℕ → Type (u + 1)} [∀ n, CommRing (A n)]
  (φ : ∀ {n m : ℕ}, n ≤ m → A m →+* A n) (ψ : ∀ n, R →+* A n)
  (hψ : ∀ {n m : ℕ} (h : n ≤ m), (φ h).comp (ψ m) = ψ n)
  (hφ : ∀ {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k), (φ h₁).comp (φ h₂) = φ (h₁.trans h₂))
  {ϖ : R} (hψ₀ : ∀ n, ψ n (ϖ ^ n) = 0)
  (hexact : ∀ a b : ℕ, Function.Exact (fun x : A (a + b) ↦ ψ (a + b) (ϖ ^ a) * x)
    (fun x ↦ ψ (a + b) (ϖ ^ b) * x))
  (hsurj : ∀ {n m : ℕ} (h : n ≤ m), Function.Surjective (φ h))
  (hker : ∀ {n m : ℕ} (h : n ≤ m), RingHom.ker (φ h) = Ideal.span {ψ m (ϖ ^ n)})
  (L : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (A n))))
  (t : ∀ n : ℕ, L (n + 1) ⟶ (Sheaf.derivedRestrictScalars J (φ n.le_succ)).obj (L n))
  (ht : ∀ n, Sheaf.IsDerivedBaseChange (t n))

include hψ₀ in
lemma smul_id_towerFunctor_obj (n : ℕ) :
    ϖ ^ n • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op n)) = 0 := by
  ext i : 1
  exact Sheaf.smul_id_restrictScalars_obj (J := J) (ψ n) (hψ₀ n) _

include hψ₀ hexact in
lemma exact_smul_towerFunctor_obj (a b : ℕ) :
    (ShortComplex.mk (ϖ ^ a • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op (a + b))))
      (ϖ ^ b • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op (a + b)))) (by
        rw [Linear.smul_comp, Category.id_comp, smul_smul, ← pow_add, add_comm,
          smul_id_towerFunctor_obj φ ψ hψ hψ₀ L t])).Exact := by
  refine HomologicalComplex.exact_of_degreewise_exact _ fun i ↦ ?_
  have hxy : ψ (a + b) (ϖ ^ a) * ψ (a + b) (ϖ ^ b) = 0 := by
    rw [← map_mul, ← pow_add, hψ₀]
  have h := (Sheaf.exact_smul_of_flat J ((towerModel (φ := fun n ↦ φ n.le_succ) L t
    (a + b)).flat i) _ _ hxy (hexact a b)).map (Sheaf.restrictScalars J (ψ (a + b)))
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, ShortComplex.map_f]
        rw [Sheaf.restrictScalars_map_smul, CategoryTheory.Functor.map_id]
        rfl)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, ShortComplex.map_g]
        rw [Sheaf.restrictScalars_map_smul, CategoryTheory.Functor.map_id]
        rfl)

include hψ₀ in
lemma quasiIso_cokernelDesc_towerFunctor_self (n : ℕ) :
    QuasiIso (cokernel.desc (ϖ ^ n • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op n)))
      ((towerFunctor φ ψ hψ L t).map (homOfLE (le_refl n)).op) (by
        rw [smul_id_towerFunctor_obj φ ψ hψ hψ₀ L t, zero_comp])) := by
  have hπ : cokernel.π (ϖ ^ n • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op n))) ≫
      cokernel.desc _ ((towerFunctor φ ψ hψ L t).map (homOfLE (le_refl n)).op) (by
        rw [smul_id_towerFunctor_obj φ ψ hψ hψ₀ L t, zero_comp]) = 𝟙 _ := by
    rw [cokernel.π_desc]
    exact (towerFunctor φ ψ hψ L t).map_id _
  have : IsIso (cokernel.desc (ϖ ^ n • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op n)))
      ((towerFunctor φ ψ hψ L t).map (homOfLE (le_refl n)).op) (by
        rw [smul_id_towerFunctor_obj φ ψ hψ hψ₀ L t, zero_comp])) :=
    ⟨cokernel.π _, by rw [← cancel_epi (cokernel.π _), reassoc_of% hπ, Category.comp_id], hπ⟩
  infer_instance

include hφ hψ₀ hsurj hker ht in
lemma quasiIso_cokernelDesc_towerFunctor (n k : ℕ) :
    QuasiIso (cokernel.desc (ϖ ^ n • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op (n + k + 1))))
      ((towerFunctor φ ψ hψ L t).map (homOfLE (Nat.le_add_right n (k + 1))).op) (by
        rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id
          ((towerFunctor φ ψ hψ L t).map _), ← Linear.comp_smul,
          smul_id_towerFunctor_obj φ ψ hψ hψ₀ L t, Limits.comp_zero])) := by
  set h := Nat.le_add_right n (k + 1)
  let M := towerModel (φ := fun n ↦ φ n.le_succ) L t
  let D := Sheaf.reductionDatum J (φ h) (hsurj h) (ψ (n + k + 1) (ϖ ^ n)) (hker h)
  have := Sheaf.restrictScalars_full J (φ h) (hsurj h)
  obtain ⟨g, hg, -⟩ := D.existsUnique_complexMap_comp (towerModelComp φ L t hφ n k)
  have hη₁ : Sheaf.IsDerivedBaseChange (Q.map (D.complexMap (M (n + k + 1)).P) ≫
      (Sheaf.restrictScalars J (φ h)).mapDerivedCategoryFactors.inv.app
        ((D.Φ.mapHomologicalComplex (.up ℤ)).obj (M (n + k + 1)).P)) :=
    fun N ↦ D.bijective_comp_map _ (M (n + k + 1)).isKFlat N
  have hη₂ := isDerivedBaseChange_towerModelComp φ L t hφ ht n k
  have : IsIso (Q.map g) := hη₁.isIso hη₂ _ (by
    rw [Category.assoc, ← Functor.mapDerivedCategoryFactors_inv_naturality, ← Category.assoc,
      ← Functor.map_comp, hg])
  have hg' : QuasiIso g := (isIso_Q_map_iff_quasiIso (φ := g)).1 this
  let ρ := ((Sheaf.restrictScalars J (ψ (n + k + 1))).mapHomologicalComplex (.up ℤ)).map
    (D.complexMap (M (n + k + 1)).P)
  have hzero : ϖ ^ n • 𝟙 (((Sheaf.restrictScalars J (ψ (n + k + 1))).mapHomologicalComplex
      (.up ℤ)).obj (((Sheaf.restrictScalars J (φ h)).mapHomologicalComplex (.up ℤ)).obj
        ((D.Φ.mapHomologicalComplex (.up ℤ)).obj (M (n + k + 1)).P))) = 0 := by
    ext i : 1
    dsimp
    change ϖ ^ n • 𝟙 ((Sheaf.restrictScalars J (ψ (n + k + 1))).obj
      ((Sheaf.restrictScalars J (φ h)).obj (D.Φ.obj ((M (n + k + 1)).P.X i)))) = 0
    rw [← CategoryTheory.Functor.map_id, ← Sheaf.restrictScalars_map_smul,
      Sheaf.smul_id_restrictScalars_obj (J := J) (φ h)
        (by
          change ((φ h).comp (ψ (n + k + 1))) (ϖ ^ n) = 0
          rw [show (φ h).comp (ψ (n + k + 1)) = ψ n from hψ h, hψ₀]), Functor.map_zero]
  have hρ : (ϖ ^ n • 𝟙 ((towerFunctor φ ψ hψ L t).obj (op (n + k + 1)))) ≫ ρ = 0 := by
    rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id ρ, ← Linear.comp_smul, hzero,
      Limits.comp_zero]
  have hS : (ShortComplex.mk _ _ hρ).Exact := by
    refine HomologicalComplex.exact_of_degreewise_exact _ fun i ↦ ?_
    refine (ShortComplex.exact_iff_of_iso ?_).1
      ((D.exact ((M (n + k + 1)).P.X i)).map (Sheaf.restrictScalars J (ψ (n + k + 1))))
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, ShortComplex.map_f]
      change (Sheaf.restrictScalars J (ψ (n + k + 1))).map
        ((ψ (n + k + 1)) (ϖ ^ n) • 𝟙 ((M (n + k + 1)).P.X i)) = _
      rw [Sheaf.restrictScalars_map_smul, CategoryTheory.Functor.map_id]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, ShortComplex.map_g]
      rfl
  have : Epi ρ := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
    have := D.epi_r ((M (n + k + 1)).P.X i)
    exact (Sheaf.restrictScalars J (ψ (n + k + 1))).map_epi (D.r.app _)
  have hT := towerFunctor_map_homOfLE φ ψ hψ L t hφ n k
  refine CochainComplex.quasiIso_cokernelDesc_of_exact_factor _ ρ hρ hS
    (((Sheaf.restrictScalars J (ψ (n + k + 1))).mapHomologicalComplex (.up ℤ)).map
        (((Sheaf.restrictScalars J (φ h)).mapHomologicalComplex (.up ℤ)).map g) ≫
        (Functor.mapHomologicalComplexCompIso (Sheaf.restrictScalarsCompIso J (ψ (n + k + 1))
          (φ (Nat.le_add_right n (k + 1))) (ψ n) (hψ _).symm) (.up ℤ)).hom.app _) _ ?_ _
  dsimp only [ρ]
  rw [← Functor.map_comp_assoc, hg]
  exact hT.symm

include hφ hψ₀ hexact hsurj hker ht in
/-- The strict model of a normalized tower is a normalized adic tower of complexes. -/
theorem isNormalizedAdicTower_towerFunctor :
    CochainComplex.IsNormalizedAdicTower ϖ (towerFunctor φ ψ hψ L t) where
  smul_eq_zero := smul_id_towerFunctor_obj φ ψ hψ hψ₀ L t
  exact_smul := exact_smul_towerFunctor_obj φ ψ hψ hψ₀ hexact L t
  quasiIso_cokernelDesc {n m} h := by
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact quasiIso_cokernelDesc_towerFunctor_self φ ψ hψ hψ₀ L t n
    · obtain ⟨k, rfl⟩ : ∃ k, m = n + k + 1 := ⟨m - n - 1, by omega⟩
      exact quasiIso_cokernelDesc_towerFunctor φ ψ hψ hφ hψ₀ hsurj hker L t ht n k

include hφ hψ₀ hexact hsurj hker ht in
/-- **Strictification of normalized towers.** A normalized tower `L_n ∈ D(J, A_n)`, whose
transition maps `t_n : L_{n+1} ⟶ Res L_n` exhibit `L_n` as a derived base change of
`L_{n+1}`, is represented by a normalized adic tower `T` of complexes of sheaves of
`R`-modules: there are isomorphisms `Q T_n ≅ Res L_n` under which the transition maps of `T`
become the restrictions of scalars of the `t_n`. -/
theorem exists_isNormalizedAdicTower :
    ∃ (T : ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{u + 1} R)) ℤ)
      (e : ∀ n : ℕ, Q.obj (T.obj (op n)) ≅ (Sheaf.derivedRestrictScalars J (ψ n)).obj (L n)),
      CochainComplex.IsNormalizedAdicTower ϖ T ∧ ∀ n : ℕ,
        Q.map (T.map (homOfLE n.le_succ).op) ≫ (e n).hom =
          (e (n + 1)).hom ≫ (Sheaf.derivedRestrictScalars J (ψ (n + 1))).map (t n) ≫
            (Sheaf.derivedRestrictScalarsCompIso J (hψ n.le_succ).symm).hom.app (L n) :=
  ⟨towerFunctor φ ψ hψ L t, towerFunctorIso φ ψ hψ L t,
    isNormalizedAdicTower_towerFunctor φ ψ hψ hφ hψ₀ hexact hsurj hker L t ht,
    Q_map_towerFunctor_map_comp_towerFunctorIso_hom φ ψ hψ L t⟩

end Normalized

section Quotient

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R)
  (hI : I = Ideal.span {ϖ})

include hI in
lemma _root_.Ideal.Quotient.mk_pow_eq_zero_of_eq_span (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (ϖ ^ n) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

include hϖ hI in
lemma _root_.Ideal.Quotient.exact_mul_mk_pow (a b : ℕ) :
    Function.Exact (fun x : R ⧸ I ^ (a + b) ↦ Ideal.Quotient.mk (I ^ (a + b)) (ϖ ^ a) * x)
      (fun x ↦ Ideal.Quotient.mk (I ^ (a + b)) (ϖ ^ b) * x) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only at hx
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨Ideal.Quotient.mk _ z, ?_⟩
    have : y = ϖ ^ a * z :=
      (mul_cancel_left_mem_nonZeroDivisors (pow_mem hϖ b)).1 (by rw [hz]; ring)
    simp only [this, map_mul]
  · rintro ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    simp only [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨z, by ring⟩

include hI in
lemma _root_.Ideal.Quotient.ker_factor_pow_eq_span {n m : ℕ} (h : n ≤ m) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) h)) =
      Ideal.span {Ideal.Quotient.mk (I ^ m) (ϖ ^ n)} := by
  rw [Ideal.Quotient.factor_ker, hI]
  simp only [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]

end Quotient

end DerivedCategory
