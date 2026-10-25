import Langlands.Cohomology.DivisibleSystem.InvariantTransition

/-!
# Transitivity of the transition maps between Harris's `C_m^{•,H}`

Harris 1999, §2, p.306, takes the direct limit of the complexes `C_m^{•,H}` as `H` shrinks to
the identity. The InvariantTransition module builds, for normal subgroups `H' ≤ H` of finite
index with `|ker (G ⧸ H' → G ⧸ H)|` invertible in `R`, the transition morphism
`quotientInvariantsTransition` from the inflation of `C_m^{•,H}` to the inflation of
`C_m^{•,H'}`. This module proves that these morphisms form a direct system: for
`H'' ≤ H' ≤ H` the transition from `H` to `H'` followed by the transition from `H'` to `H''` is
the transition from `H` to `H''` (`quotientInvariantsTransition_comp`), and the transition from
`H` to itself is the identity (`quotientInvariantsTransition_refl`).

The proofs rest on generic lemmas about maps of augmented endofunctors (`StandardMap`): the
composite `StandardMap.comp` along `Φ₁ ⋙ Φ₂`, the compatibility of `totalMap` with composites
and with natural transformations `Φ ⟶ Φ'` (`StandardMap.map_totalMap_comp_totalMap`,
`StandardMap.totalMapF_comp_map_id`), and on the composition and identity laws of the normalized
fiber sums of the StandardMap module (`fiberAverage_comp`, `fiberAverage_comp_resIdHom`).

The direct limit over `H` and Harris's (2.6) are not constructed.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w uR uG uV u v u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace StandardMap

section Comp

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] {Φ₁ : A ⥤ B} {Φ₂ : B ⥤ C} {P : A ⥤ A} {ε : P ⟶ 𝟭 A}
  {Q : B ⥤ B} {η : Q ⟶ 𝟭 B} {S : C ⥤ C} {σ : S ⟶ 𝟭 C} (t₁ : StandardMap Φ₁ P ε Q η)
  (t₂ : StandardMap Φ₂ Q η S σ) (t₃ : StandardMap (Φ₁ ⋙ Φ₂) P ε S σ)

/-- The composite of maps of augmented endofunctors along `Φ₁` and along `Φ₂`: the comparison
`Φ₂ (Φ₁ (P X)) ⟶ Φ₂ (Q (Φ₁ X)) ⟶ S (Φ₂ (Φ₁ X))`. -/
@[simps]
def comp : StandardMap (Φ₁ ⋙ Φ₂) P ε S σ where
  θ :=
    { app X := Φ₂.map (t₁.θ.app X) ≫ t₂.θ.app (Φ₁.obj X)
      naturality X Y f := by
        have h₁ := congrArg Φ₂.map (t₁.θ.naturality f)
        have h₂ := t₂.θ.naturality (Φ₁.map f)
        rw [Functor.comp_map, Functor.comp_map, Φ₂.map_comp, Φ₂.map_comp] at h₁
        rw [Functor.comp_map, Functor.comp_map] at h₂
        change Φ₂.map (Φ₁.map (P.map f)) ≫ Φ₂.map (t₁.θ.app Y) ≫ t₂.θ.app (Φ₁.obj Y) =
          (Φ₂.map (t₁.θ.app X) ≫ t₂.θ.app (Φ₁.obj X)) ≫ S.map (Φ₂.map (Φ₁.map f))
        rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc] }
  θ_comp_η X := by
    change (Φ₂.map (t₁.θ.app X) ≫ t₂.θ.app (Φ₁.obj X)) ≫ σ.app (Φ₂.obj (Φ₁.obj X)) =
      Φ₂.map (Φ₁.map (ε.app X))
    rw [Category.assoc, t₂.θ_comp_η, ← Φ₂.map_comp, t₁.θ_comp_η]

/-- If the comparison `θ` along `Φ₁ ⋙ Φ₂` is `Φ₂` of the comparison along `Φ₁` followed by the
comparison along `Φ₂`, then so are all iterated comparisons. -/
lemma powApp_comp (hθ : ∀ X, Φ₂.map (t₁.θ.app X) ≫ t₂.θ.app (Φ₁.obj X) = t₃.θ.app X)
    (n : ℕ) (X : A) :
    Φ₂.map (t₁.powApp n X) ≫ t₂.powApp n (Φ₁.obj X) = t₃.powApp n X := by
  induction n with
  | zero =>
    change Φ₂.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
    rw [Φ₂.map_id, Category.comp_id]
  | succ n ih =>
    have h := t₂.θ.naturality (t₁.powApp n X)
    rw [Functor.comp_map, Functor.comp_map] at h
    change Φ₂.map (t₁.θ.app ((standardPow P n).obj X) ≫ Q.map (t₁.powApp n X)) ≫
        t₂.θ.app ((standardPow Q n).obj (Φ₁.obj X)) ≫ S.map (t₂.powApp n (Φ₁.obj X)) =
      t₃.θ.app ((standardPow P n).obj X) ≫ S.map (t₃.powApp n X)
    rw [Φ₂.map_comp, Category.assoc, ← Category.assoc (Φ₂.map (Q.map _)), h, Category.assoc,
      ← S.map_comp, ih, ← Category.assoc, hθ]

end Comp

section Map

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {Φ Φ' : A ⥤ B}
  {P : A ⥤ A} {ε : P ⟶ 𝟭 A} {Q : B ⥤ B} {η : Q ⟶ 𝟭 B} (t : StandardMap Φ P ε Q η)
  (t' : StandardMap Φ' P ε Q η) (e : Φ ⟶ Φ')

/-- If `e : Φ ⟶ Φ'` intertwines the comparisons `θ` and `θ'`, it intertwines all iterated
comparisons. -/
lemma powApp_comp_map (hθ : ∀ X, t.θ.app X ≫ Q.map (e.app X) = e.app (P.obj X) ≫ t'.θ.app X)
    (n : ℕ) (X : A) :
    t.powApp n X ≫ (standardPow Q n).map (e.app X) =
      e.app ((standardPow P n).obj X) ≫ t'.powApp n X := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ e.app X = e.app X ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  | succ n ih =>
    change (t.θ.app ((standardPow P n).obj X) ≫ Q.map (t.powApp n X)) ≫
        Q.map ((standardPow Q n).map (e.app X)) =
      e.app (P.obj ((standardPow P n).obj X)) ≫ t'.θ.app ((standardPow P n).obj X) ≫
        Q.map (t'.powApp n X)
    rw [Category.assoc, ← Q.map_comp, ih, Q.map_comp, ← Category.assoc, hθ, Category.assoc]

variable [Abelian A] [Abelian B] [Φ.Additive] [Φ'.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteColimits Φ] [PreservesFiniteColimits Φ'] (N : ℕ) (L : CochainComplex A ℕ)

/-- Degree `n` of `totalMap_comp_map`. -/
lemma totalMapF_comp_map
    (hθ : ∀ X, t.θ.app X ≫ Q.map (e.app X) = e.app (P.obj X) ≫ t'.θ.app X) (n : ℤ) :
    t.totalMapF N L n ≫ (HomologicalComplex₂.total.map (((upFinEmbedding N).restrictionFunctor _).map
        (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℕ)).app L)))
            (ComplexShape.up ℤ)).f n =
      e.app (((standardRows N P ε L).total (ComplexShape.up ℤ)).X n) ≫ t'.totalMapF N L n := by
  refine totalMap_hom_ext fun q r h => ?_
  have hmap := HomologicalComplex₂.ιTotal_map _ _
    (((upFinEmbedding N).restrictionFunctor _).map
      (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℕ)).app L)))
    (ComplexShape.up ℤ) q r n h
  rw [map_ιTotal_totalMapF_assoc, hmap, e.naturality_assoc, t'.map_ιTotal_totalMapF,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) (t.powApp_comp_map t' e hθ (r + 1) (L.X q))

/-- If `e : Φ ⟶ Φ'` intertwines the comparisons `θ` and `θ'`, then `totalMap` along `Φ` followed
by the map of total complexes induced by `e` at `L` is `e` followed by `totalMap` along `Φ'`. -/
lemma totalMap_comp_map
    (hθ : ∀ X, t.θ.app X ≫ Q.map (e.app X) = e.app (P.obj X) ≫ t'.θ.app X) :
    t.totalMap N L ≫ (upFinTotalFunctor B N).map
        (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℕ)).app L)) =
      (NatTrans.mapHomologicalComplex e (ComplexShape.up ℤ)).app
          ((standardRows N P ε L).total (ComplexShape.up ℤ)) ≫ t'.totalMap N L :=
  HomologicalComplex.hom_ext _ _ fun n => t.totalMapF_comp_map t' e N L hθ n

end Map

section Id

variable {A : Type u₁} [Category.{v₁} A] {Φ : A ⥤ A} {P : A ⥤ A} {ε : P ⟶ 𝟭 A}
  (t : StandardMap Φ P ε P ε) (e : Φ ⟶ 𝟭 A)

/-- If `e : Φ ⟶ 𝟭` turns the comparison `θ` into the identity, it turns all iterated
comparisons into the identity. -/
lemma powApp_comp_map_id (hθ : ∀ X, t.θ.app X ≫ P.map (e.app X) = e.app (P.obj X)) (n : ℕ)
    (X : A) :
    t.powApp n X ≫ (standardPow P n).map (e.app X) = e.app ((standardPow P n).obj X) := by
  induction n with
  | zero =>
    change 𝟙 _ ≫ e.app X = e.app X
    rw [Category.id_comp]
  | succ n ih =>
    change (t.θ.app ((standardPow P n).obj X) ≫ P.map (t.powApp n X)) ≫
        P.map ((standardPow P n).map (e.app X)) = e.app (P.obj ((standardPow P n).obj X))
    rw [Category.assoc, ← P.map_comp, ih, hθ]

variable [Abelian A] [Φ.Additive] [P.Additive] [PreservesFiniteColimits Φ] (N : ℕ)
  (L : CochainComplex A ℕ)

/-- If `e : Φ ⟶ 𝟭` turns the comparison `θ` into the identity, then, in each degree, `totalMap`
followed by the map of total complexes induced by `e` at `L` is `e`. -/
lemma totalMapF_comp_map_id (hθ : ∀ X, t.θ.app X ≫ P.map (e.app X) = e.app (P.obj X))
    (n : ℤ) :
    t.totalMapF N L n ≫ (HomologicalComplex₂.total.map (((upFinEmbedding N).restrictionFunctor _).map
        (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℕ)).app L)))
            (ComplexShape.up ℤ)).f n =
      e.app (((standardRows N P ε L).total (ComplexShape.up ℤ)).X n) := by
  refine totalMap_hom_ext fun q r h => ?_
  have hmap := HomologicalComplex₂.ιTotal_map _ _
    (((upFinEmbedding N).restrictionFunctor _).map
      (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℕ)).app L)))
    (ComplexShape.up ℤ) q r n h
  rw [map_ιTotal_totalMapF_assoc, hmap, e.naturality, ← Category.assoc]
  exact congrArg (· ≫ _) (t.powApp_comp_map_id e hθ (r + 1) (L.X q))

end Id

section CompTotal

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] {Φ₁ : A ⥤ B} {Φ₂ : B ⥤ C} {P : A ⥤ A}
  {ε : P ⟶ 𝟭 A} {Q : B ⥤ B} {η : Q ⟶ 𝟭 B} {S : C ⥤ C} {σ : S ⟶ 𝟭 C} [Φ₁.Additive]
  [Φ₂.Additive] [P.Additive] [Q.Additive] [S.Additive] [PreservesFiniteColimits Φ₁]
  [PreservesFiniteColimits Φ₂] (t₁ : StandardMap Φ₁ P ε Q η) (t₂ : StandardMap Φ₂ Q η S σ)
  (N : ℕ) (L : CochainComplex A ℕ)

/-- Degree `n` of `totalMap_comp`. -/
lemma totalMapF_comp (n : ℤ) :
    (t₁.comp t₂).totalMapF N L n =
      Φ₂.map (t₁.totalMapF N L n) ≫
        t₂.totalMapF N ((Φ₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) n := by
  refine totalMap_hom_ext fun q r h => ?_
  refine ((t₁.comp t₂).map_ιTotal_totalMapF N L n q r h).trans ?_
  refine Eq.trans ?_ (Φ₂.map_comp_assoc _ _ _)
  rw [t₁.map_ιTotal_totalMapF, Φ₂.map_comp_assoc, t₂.map_ιTotal_totalMapF, ← Category.assoc]
  exact congrArg (· ≫ _) (t₁.powApp_comp t₂ (t₁.comp t₂) (fun _ => rfl) (r + 1) (L.X q)).symm

/-- `totalMap` for the composite `t₁.comp t₂` is `Φ₂` of `totalMap` for `t₁` followed by
`totalMap` for `t₂`. -/
lemma totalMap_comp :
    (t₁.comp t₂).totalMap N L =
      (Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (t₁.totalMap N L) ≫
        t₂.totalMap N ((Φ₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) :=
  HomologicalComplex.hom_ext _ _ fun n => t₁.totalMapF_comp t₂ N L n

variable {Φ₃ : A ⥤ C} [Φ₃.Additive] [PreservesFiniteColimits Φ₃] (t₃ : StandardMap Φ₃ P ε S σ)
  (e : Φ₁ ⋙ Φ₂ ⟶ Φ₃)

/-- Given `e : Φ₁ ⋙ Φ₂ ⟶ Φ₃` intertwining the comparison of `t₁.comp t₂` with that of `t₃`, and
morphisms of complexes `c₁ : Φ₁ L ⟶ L'`, `c₂ : Φ₂ L' ⟶ L''`, `c₃ : Φ₃ L ⟶ L''` with
`Φ₂ c₁ ≫ c₂ = e_L ≫ c₃`: `Φ₂` of (`totalMap` for `t₁` followed by the map of total complexes
induced by `c₁`), followed by `totalMap` for `t₂` and the map induced by `c₂`, is `e` followed by
`totalMap` for `t₃` and the map induced by `c₃`. -/
lemma map_totalMap_comp_totalMap
    (hθ : ∀ X, (Φ₂.map (t₁.θ.app X) ≫ t₂.θ.app (Φ₁.obj X)) ≫ S.map (e.app X) =
      e.app (P.obj X) ≫ t₃.θ.app X)
    {L' : CochainComplex B ℕ} {L'' : CochainComplex C ℕ}
    (c₁ : (Φ₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj L ⟶ L')
    (c₂ : (Φ₂.mapHomologicalComplex (ComplexShape.up ℕ)).obj L' ⟶ L'')
    (c₃ : (Φ₃.mapHomologicalComplex (ComplexShape.up ℕ)).obj L ⟶ L'')
    (hc : (Φ₂.mapHomologicalComplex (ComplexShape.up ℕ)).map c₁ ≫ c₂ =
      (NatTrans.mapHomologicalComplex e (ComplexShape.up ℕ)).app L ≫ c₃) :
    (Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (t₁.totalMap N L ≫
        (upFinTotalFunctor B N).map
          (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map c₁)) ≫
      t₂.totalMap N L' ≫ (upFinTotalFunctor C N).map
        (((standardResolution S σ).mapHomologicalComplex (ComplexShape.up ℕ)).map c₂) =
    (NatTrans.mapHomologicalComplex e (ComplexShape.up ℤ)).app
        ((standardRows N P ε L).total (ComplexShape.up ℤ)) ≫ t₃.totalMap N L ≫
      (upFinTotalFunctor C N).map
        (((standardResolution S σ).mapHomologicalComplex (ComplexShape.up ℕ)).map c₃) := by
  have h₁ := t₂.totalMap_naturality N c₁
  have h₂ := t₁.totalMap_comp t₂ N L
  have h₃ := (t₁.comp t₂).totalMap_comp_map t₃ e N L hθ
  let T := (standardResolution S σ).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    upFinTotalFunctor C N
  have hc' : T.map ((Φ₂.mapHomologicalComplex (ComplexShape.up ℕ)).map c₁) ≫ T.map c₂ =
      T.map ((NatTrans.mapHomologicalComplex e (ComplexShape.up ℕ)).app L) ≫ T.map c₃ :=
    (T.map_comp _ _).symm.trans ((congrArg T.map hc).trans (T.map_comp _ _))
  refine (congrArg (· ≫ t₂.totalMap N L' ≫ (upFinTotalFunctor C N).map
      (((standardResolution S σ).mapHomologicalComplex (ComplexShape.up ℕ)).map c₂))
    ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).map_comp (t₁.totalMap N L)
      ((upFinTotalFunctor B N).map
        (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map c₁)))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  have h₁' := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (upFinTotalFunctor C N).map
    (((standardResolution S σ).mapHomologicalComplex (ComplexShape.up ℕ)).map c₂)) h₁).trans
      (Category.assoc _ _ _))
  refine (congrArg ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (t₁.totalMap N L) ≫ ·)
    h₁').trans ?_
  refine (congrArg ((Φ₂.mapHomologicalComplex (ComplexShape.up ℤ)).map (t₁.totalMap N L) ≫
    t₂.totalMap N ((Φ₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) ≫ ·) hc').trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h₂.symm).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ _) h₃).trans (Category.assoc _ _ _)

end CompTotal

end StandardMap

section GroupComp

open Representation

variable (k : Type u) [CommRing k] {Γ Γ' Γ'' : Type v} [Group Γ] [Group Γ'] [Group Γ'']
  (π₁ : Γ' →* Γ) (π₂ : Γ'' →* Γ') (π₃ : Γ'' →* Γ) (h : ∀ g, π₁ (π₂ g) = π₃ g)

include h

/-- For `π₁ ∘ π₂ = π₃` pointwise, the identity maps `Res_π₂ (Res_π₁ V) ⟶ Res_π₃ V`. -/
def resCompHom :
    Rep.resFunctor.{max w u v} (k := k) π₁ ⋙ Rep.resFunctor π₂ ⟶ Rep.resFunctor π₃ where
  app V := Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun x => by
    change V.ρ (π₁ (π₂ g)) x = V.ρ (π₃ g) x
    rw [h]⟩
  naturality _ _ _ := by
    ext
    rfl

lemma resCompHom_app_hom_apply (V : Rep.{max w u v} k Γ) (x : V) :
    ((resCompHom.{w} k π₁ π₂ π₃ h).app V).hom x = x :=
  rfl

variable [Fintype Γ'] [Fintype Γ''] [DecidableEq Γ] [DecidableEq Γ']

/-- Summing over the fibers of `π₂` above the fiber of `π₁` over `γ` is summing over the fiber of
`π₃` over `γ`. -/
lemma sum_filter_comp {M : Type*} [AddCommMonoid M] (f : Γ'' → M) (γ : Γ) :
    ∑ γ' ∈ Finset.univ.filter (π₁ · = γ), ∑ γ'' ∈ Finset.univ.filter (π₂ · = γ'), f γ'' =
      ∑ γ'' ∈ Finset.univ.filter (π₃ · = γ), f γ'' := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := π₂) (t := Finset.univ.filter (π₁ · = γ))
    (fun γ'' hγ'' => by
      rw [Finset.mem_filter] at hγ'' ⊢
      exact ⟨Finset.mem_univ _, (h γ'').trans hγ''.2⟩)]
  refine Finset.sum_congr rfl fun γ' hγ' => Finset.sum_congr ?_ fun _ _ => rfl
  ext γ''
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ' ⊢
  constructor
  · intro h₂
    exact ⟨by rw [← h, h₂, hγ'], h₂⟩
  · exact fun h' => h'.2

/-- For surjective `π₁`, `π₂` with `π₁ ∘ π₂ = π₃`, `|ker π₃| = |ker π₁| |ker π₂|`. -/
lemma nat_card_ker_comp (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂) :
    Nat.card π₃.ker = Nat.card π₁.ker * Nat.card π₂.ker := by
  have hπ₃ : Function.Surjective π₃ := fun γ => by
    obtain ⟨γ', rfl⟩ := hπ₁ γ
    obtain ⟨γ'', rfl⟩ := hπ₂ γ'
    exact ⟨γ'', (h γ'').symm⟩
  have hs := sum_filter_comp π₁ π₂ π₃ h (fun _ => (1 : ℕ)) 1
  simp only [Finset.sum_const, smul_eq_mul, mul_one, card_filter_eq_nat_card_ker π₂ hπ₂,
    card_filter_eq_nat_card_ker π₁ hπ₁, card_filter_eq_nat_card_ker π₃ hπ₃] at hs
  exact hs.symm

/-- The normalized fiber sums compose: along `π₂` after along `π₁` is along `π₃`, up to the
identifications `resCompHom`, when `π₁` and `π₂` are surjective. -/
lemma fiberAverage_comp (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂)
    (V : Rep.{max w u v} k Γ) :
    ((Rep.resFunctor π₂).map ((fiberAverage.{w} k π₁).app V) ≫
        (fiberAverage.{w} k π₂).app ((Rep.resFunctor π₁).obj V)) ≫
      (indResBot.{w} k Γ'').map ((resCompHom.{w} k π₁ π₂ π₃ h).app V) =
    (resCompHom.{w} k π₁ π₂ π₃ h).app ((indResBot.{w} k Γ).obj V) ≫
      (fiberAverage.{w} k π₃).app V := by
  refine Rep.hom_ext <| IntertwiningMap.ext <| IndV.hom_ext _ _ fun γ => LinearMap.ext fun x => ?_
  change ((indResBot.{w} k Γ'').map ((resCompHom.{w} k π₁ π₂ π₃ h).app V)).hom
      (((fiberAverage.{w} k π₂).app ((Rep.resFunctor π₁).obj V)).hom
        (((fiberAverage.{w} k π₁).app V).hom (IndV.mk _ _ γ x))) =
    ((fiberAverage.{w} k π₃).app V).hom (IndV.mk _ _ γ x)
  rw [fiberAverage_app_mk, fiberAverage_app_mk, map_smul, map_sum, map_smul, map_sum]
  have h₂ : ∀ γ' ∈ Finset.univ.filter (π₁ · = γ),
      ((indResBot.{w} k Γ'').map ((resCompHom.{w} k π₁ π₂ π₃ h).app V)).hom
        (((fiberAverage.{w} k π₂).app ((Rep.resFunctor π₁).obj V)).hom
          (IndV.mk (⊥ : Subgroup Γ').subtype ((V.ρ.comp π₁).comp (⊥ : Subgroup Γ').subtype) γ' x)) =
      Ring.inverse (Nat.card π₂.ker : k) • ∑ γ'' ∈ Finset.univ.filter (π₂ · = γ'),
        IndV.mk (⊥ : Subgroup Γ'').subtype ((V.ρ.comp π₃).comp (⊥ : Subgroup Γ'').subtype)
          γ'' x := fun γ' _ => by
    refine (congrArg ((indResBot.{w} k Γ'').map ((resCompHom.{w} k π₁ π₂ π₃ h).app V)).hom
      (fiberAverage_app_mk.{w} k π₂ ((Rep.resFunctor π₁).obj V) γ' x)).trans ?_
    rw [map_smul, map_sum]
    exact congrArg (_ • ·) (Finset.sum_congr rfl fun _ _ => rfl)
  refine (congrArg (Ring.inverse (Nat.card π₁.ker : k) • ·) (Finset.sum_congr rfl h₂)).trans ?_
  rw [← Finset.smul_sum, smul_smul, sum_filter_comp π₁ π₂ π₃ h, nat_card_ker_comp π₁ π₂ π₃ h hπ₁ hπ₂,
    Nat.cast_mul, Ring.mul_inverse_rev, mul_comm]

end GroupComp

section GroupId

open Representation

variable (k : Type u) [CommRing k] {Γ : Type v} [Group Γ] (π : Γ →* Γ) (h : ∀ g, π g = g)

/-- For `π` pointwise the identity, the identity maps `Res_π V ⟶ V`. -/
def resIdHom : Rep.resFunctor.{max w u v} (k := k) π ⟶ 𝟭 (Rep.{max w u v} k Γ) where
  app V := Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun x => by
    change V.ρ (π g) x = V.ρ g x
    rw [h]⟩
  naturality _ _ _ := by
    ext
    rfl

variable [Fintype Γ] [DecidableEq Γ]

/-- For `π` pointwise the identity, the normalized fiber sum along `π` is the identity, up to the
identification `resIdHom`. -/
lemma fiberAverage_comp_resIdHom (V : Rep.{max w u v} k Γ) :
    (fiberAverage.{w} k π).app V ≫ (indResBot.{w} k Γ).map ((resIdHom.{w} k π h).app V) =
      (resIdHom.{w} k π h).app ((indResBot.{w} k Γ).obj V) := by
  have hπ : Function.Surjective π := fun γ => ⟨γ, h γ⟩
  refine Rep.hom_ext <| IntertwiningMap.ext <| IndV.hom_ext _ _ fun γ => LinearMap.ext fun x => ?_
  have hfilter : Finset.univ.filter (π · = γ) = {γ} := by
    ext γ'
    simp [h]
  change ((indResBot.{w} k Γ).map ((resIdHom.{w} k π h).app V)).hom
      (((fiberAverage.{w} k π).app V).hom (IndV.mk _ _ γ x)) = IndV.mk _ _ γ x
  rw [fiberAverage_app_mk, map_smul, map_sum, hfilter, Finset.sum_singleton,
    ← card_filter_eq_nat_card_ker π hπ γ, hfilter, Finset.card_singleton, Nat.cast_one,
    Ring.inverse_one, one_smul]
  rfl

end GroupId

namespace DivisibleSystem

section Transitivity

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ) (N : ℕ)

/-- In each level and degree, the transition morphism is the inflation of `totalMap` for the
normalized fiber sum followed by the map of total complexes induced by the inclusion of the
`H`-invariants into the `H'`-invariants. -/
lemma quotientInvariantsTransition_tower_app_f {H H' : Subgroup G} [H.Normal] [H'.Normal]
    [H.FiniteIndex] [H'.FiniteIndex] [Fintype (G ⧸ H')] [DecidableEq (G ⧸ H)] (hHH' : H' ≤ H)
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hK' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H').map ((K.projection h).f q)))
    (hk : IsUnit (Nat.card (quotientProjection hHH').ker : R)) (m : ℕ) (n : ℤ) :
    ((quotientInvariantsTransition.{w, uR, uG} K hHH' N hK hK' hk).tower.app (op m)).f n =
      (Rep.quotientInflation.{uR, uG, max w uR uG} R H').map
        (((groupStandardMap.{w, uG, uR} R (quotientProjection hHH')
            (surjective_quotientProjection hHH') hk).totalMap N
              ((K.quotientInvariantsComplexes H hK).obj m) ≫
          (upFinTotalFunctor (Rep.{max w uR uG} R (G ⧸ H')) N).map
            (((standardResolution (indResBot.{w, uG, uR} R (G ⧸ H'))
                (indResBotCounit.{w, uG, uR} R (G ⧸ H'))).mapHomologicalComplex
                  (ComplexShape.up ℕ)).map
              ((quotientInvariantsComplexesChange.{w, uR, uG} K hHH' hK hK').tower.app
                (op m)))).f n) :=
  Category.id_comp _

omit [TopologicalSpace G] in
/-- If the orders of the kernels of `G ⧸ H' → G ⧸ H` and `G ⧸ H'' → G ⧸ H'` are units in `R`, so
is the order of the kernel of `G ⧸ H'' → G ⧸ H`. -/
lemma isUnit_card_ker_quotientProjection_trans {H H' H'' : Subgroup G} [H.Normal] [H'.Normal]
    [H''.Normal] [Fintype (G ⧸ H')] [Fintype (G ⧸ H'')] [DecidableEq (G ⧸ H)]
    [DecidableEq (G ⧸ H')] (hHH' : H' ≤ H) (hH'H'' : H'' ≤ H')
    (hk : IsUnit (Nat.card (quotientProjection hHH').ker : R))
    (hk' : IsUnit (Nat.card (quotientProjection hH'H'').ker : R)) :
    IsUnit (Nat.card (quotientProjection (hH'H''.trans hHH')).ker : R) := by
  rw [nat_card_ker_comp (quotientProjection hHH') (quotientProjection hH'H'')
    (quotientProjection (hH'H''.trans hHH')) (fun g => QuotientGroup.induction_on g fun _ => rfl)
    (surjective_quotientProjection hHH') (surjective_quotientProjection hH'H''), Nat.cast_mul]
  exact hk.mul hk'

/-- The transition morphisms compose: for normal subgroups `H'' ≤ H' ≤ H` of finite index, the
transition from `H` to `H'` followed by the transition from `H'` to `H''` is the transition from
`H` to `H''`. -/
theorem quotientInvariantsTransition_comp {H H' H'' : Subgroup G} [H.Normal] [H'.Normal]
    [H''.Normal] [H.FiniteIndex] [H'.FiniteIndex] [H''.FiniteIndex] [Fintype (G ⧸ H')]
    [Fintype (G ⧸ H'')] [DecidableEq (G ⧸ H)] [DecidableEq (G ⧸ H')] (hHH' : H' ≤ H)
    (hH'H'' : H'' ≤ H')
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hK' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H').map ((K.projection h).f q)))
    (hK'' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H'').map ((K.projection h).f q)))
    (hk : IsUnit (Nat.card (quotientProjection hHH').ker : R))
    (hk' : IsUnit (Nat.card (quotientProjection hH'H'').ker : R)) :
    quotientInvariantsTransition.{w, uR, uG} K hHH' N hK hK' hk ≫
        quotientInvariantsTransition.{w, uR, uG} K hH'H'' N hK' hK'' hk' =
      quotientInvariantsTransition.{w, uR, uG} K (hH'H''.trans hHH') N hK hK''
        (isUnit_card_ker_quotientProjection_trans hHH' hH'H'' hk hk') := by
  have hk'' := isUnit_card_ker_quotientProjection_trans hHH' hH'H'' hk hk'
  refine hom_ext (NatTrans.ext (funext fun m => HomologicalComplex.hom_ext _ _ fun n => ?_))
  obtain ⟨m⟩ := m
  have hc : ((Rep.resFunctor.{max w uR uG} (k := R)
        (quotientProjection hH'H'')).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((quotientInvariantsComplexesChange.{w, uR, uG} K hHH' hK hK').tower.app (op m)) ≫
      (quotientInvariantsComplexesChange.{w, uR, uG} K hH'H'' hK' hK'').tower.app (op m) =
      (NatTrans.mapHomologicalComplex (resCompHom.{w, uR, uG} R (quotientProjection hHH')
          (quotientProjection hH'H'') (quotientProjection (hH'H''.trans hHH'))
          (fun g => QuotientGroup.induction_on g fun _ => rfl)) (ComplexShape.up ℕ)).app
          ((K.quotientInvariantsComplexes H hK).obj m) ≫
        (quotientInvariantsComplexesChange.{w, uR, uG} K (hH'H''.trans hHH') hK hK'').tower.app
          (op m) :=
    HomologicalComplex.hom_ext _ _ fun q => by
      ext x
      rfl
  have key := congrArg (fun φ => φ.f n) (StandardMap.map_totalMap_comp_totalMap
    (groupStandardMap.{w, uG, uR} R (quotientProjection hHH')
      (surjective_quotientProjection hHH') hk)
    (groupStandardMap.{w, uG, uR} R (quotientProjection hH'H'')
      (surjective_quotientProjection hH'H'') hk')
    N ((K.quotientInvariantsComplexes H hK).obj m)
    (groupStandardMap.{w, uG, uR} R (quotientProjection (hH'H''.trans hHH'))
      (surjective_quotientProjection (hH'H''.trans hHH')) hk'')
    (resCompHom.{w, uR, uG} R (quotientProjection hHH') (quotientProjection hH'H'')
      (quotientProjection (hH'H''.trans hHH'))
      (fun g => QuotientGroup.induction_on g fun _ => rfl))
    (fun V => fiberAverage_comp.{w, uR, uG} R _ _ _ _ (surjective_quotientProjection hHH')
      (surjective_quotientProjection hH'H'') V) _ _ _ hc)
  have key' := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (Rep.quotientInflation.{uR, uG, max w uR uG} R H'').map key).trans
      (Functor.map_comp _ _ _))
  rw [comp_tower, NatTrans.comp_app, HomologicalComplex.comp_f,
    quotientInvariantsTransition_tower_app_f.{w, uR, uG} K N hHH' hK hK' hk m n,
    quotientInvariantsTransition_tower_app_f.{w, uR, uG} K N hH'H'' hK' hK'' hk' m n,
    quotientInvariantsTransition_tower_app_f.{w, uR, uG} K N (hH'H''.trans hHH') hK hK'' hk'' m n]
  refine key'.trans ?_
  ext x
  rfl

/-- The transition morphism from `H` to itself is the identity. -/
theorem quotientInvariantsTransition_refl {H : Subgroup G} [H.Normal] [H.FiniteIndex]
    [Fintype (G ⧸ H)] [DecidableEq (G ⧸ H)]
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hk : IsUnit (Nat.card (quotientProjection (le_refl H)).ker : R)) :
    quotientInvariantsTransition.{w, uR, uG} K (le_refl H) N hK hK hk = 𝟙 _ := by
  refine hom_ext (NatTrans.ext (funext fun m => HomologicalComplex.hom_ext _ _ fun n => ?_))
  obtain ⟨m⟩ := m
  have hc : (quotientInvariantsComplexesChange.{w, uR, uG} K (le_refl H) hK hK).tower.app (op m) =
      (NatTrans.mapHomologicalComplex (resIdHom.{w, uR, uG} R (quotientProjection (le_refl H))
          (fun g => QuotientGroup.induction_on g fun _ => rfl)) (ComplexShape.up ℕ)).app
        ((K.quotientInvariantsComplexes H hK).obj m) :=
    HomologicalComplex.hom_ext _ _ fun q => by
      ext x
      rfl
  have key := StandardMap.totalMapF_comp_map_id
    (groupStandardMap.{w, uG, uR} R (quotientProjection (le_refl H))
      (surjective_quotientProjection (le_refl H)) hk)
    (resIdHom.{w, uR, uG} R (quotientProjection (le_refl H))
      (fun g => QuotientGroup.induction_on g fun _ => rfl)) N
    ((K.quotientInvariantsComplexes H hK).obj m)
    (fun V => fiberAverage_comp_resIdHom.{w, uR, uG} R _ _ V) n
  rw [quotientInvariantsTransition_tower_app_f.{w, uR, uG} K N (le_refl H) hK hK hk m n, hc,
    id_tower, NatTrans.id_app, HomologicalComplex.id_f]
  refine (congrArg (Rep.quotientInflation.{uR, uG, max w uR uG} R H).map key).trans ?_
  ext x
  rfl

end Transitivity

end DivisibleSystem

end Langlands.Cohomology
