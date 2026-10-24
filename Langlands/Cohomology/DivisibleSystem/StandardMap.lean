import Langlands.Cohomology.DivisibleSystem.TotalExact
import Langlands.Cohomology.DerivedPlus

/-!
# Maps of standard resolutions along a functor

For augmentations `ε : P ⟶ 𝟭 A` and `η : Q ⟶ 𝟭 B` and a functor `Φ : A ⥤ B`, a
`StandardMap Φ P ε Q η` is a natural transformation `θ : P ⋙ Φ ⟶ Φ ⋙ Q` compatible with the
augmentations. It induces:

* `StandardMap.powApp`: the iterated comparisons `Φ (P^n X) ⟶ Q^n (Φ X)`, which commute with the
  differentials (`StandardMap.map_differential_comp_powApp`);
* `StandardMap.resolution`: the map from `Φ` of the standard resolution along `P` to the standard
  resolution along `Q` of `Φ`, compatible with the augmentations;
* `StandardMap.totalMap`: for `Φ` additive and preserving finite colimits, the map from `Φ` of the
  total complex of the standard resolutions (rows `q < N`) of a complex `L` to the total complex
  for `Φ L`, natural in `L`, compatible with the morphisms to `L` and `Φ L` extended to `ℤ`
  (`StandardMap.totalMap_comp_toExtend`), and a quasi-isomorphism when `Φ` is exact and both
  totalized augmentations are (`StandardMap.quasiIso_totalMap`);
* `StandardMap.standardTotalSystemMap`: the corresponding morphism of `ℓ`-divisible systems.

For a surjective homomorphism `π : Γ' →* Γ` of groups, `Γ'` finite, with `|ker π|` invertible in
`k`, the normalized fiber sum `⟦γ ⊗ v⟧ ↦ |ker π|⁻¹ • ∑_{π γ' = γ} ⟦γ' ⊗ v⟧` is a `StandardMap`
along `Res_π` from `Ind_1^Γ Res_1^Γ` to `Ind_1^Γ' Res_1^Γ'` (`groupStandardMap`), giving
`DivisibleSystem.groupStandardTotalSystemMap` and its level-wise quasi-isomorphism.

Harris (1999), p.306, compares `C_m^{•,H}` and `C_m^{•,H'}` for `H' ⊆ H` normal in `S(ẽ)`; there
`π` would be the projection `S(ẽ)/H' → S(ẽ)/H`. This module does not formalize that comparison.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

section ExtendXIso

open HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι} {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D)
  [F.PreservesZeroMorphisms] (K : HomologicalComplex C c)

/-- On a term of the extension that comes from `K`, the comparison `DerivedPlus.extendXMapIso`
identifies `F` of Mathlib's identification `extend.XIso` with the identification for `F K`. -/
lemma map_extendXIso_inv_comp {j : Option ι} {i : ι} (h : j = some i) :
    F.map (extend.XIso K h).inv ≫ (DerivedPlus.extendXMapIso F K j).inv =
      (extend.XIso ((F.mapHomologicalComplex c).obj K) h).inv := by
  subst h
  simp [extend.XIso, DerivedPlus.extendXMapIso, eqToHom_map]
  exact Category.comp_id _

end ExtendXIso

section StandardMap

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- A map of augmented endofunctors along a functor `Φ : A ⥤ B`: a natural transformation
`θ : P ⋙ Φ ⟶ Φ ⋙ Q` compatible with the augmentations `ε : P ⟶ 𝟭 A` and `η : Q ⟶ 𝟭 B`. -/
structure StandardMap (Φ : A ⥤ B) (P : A ⥤ A) (ε : P ⟶ 𝟭 A) (Q : B ⥤ B) (η : Q ⟶ 𝟭 B) where
  /-- The comparison `Φ (P X) ⟶ Q (Φ X)`. -/
  θ : P ⋙ Φ ⟶ Φ ⋙ Q
  /-- Compatibility with the augmentations. -/
  θ_comp_η (X : A) : θ.app X ≫ η.app (Φ.obj X) = Φ.map (ε.app X)

namespace StandardMap

variable {Φ : A ⥤ B} {P : A ⥤ A} {ε : P ⟶ 𝟭 A} {Q : B ⥤ B} {η : Q ⟶ 𝟭 B}
  (t : StandardMap Φ P ε Q η)

/-- The iterated comparisons `Φ (P^n X) ⟶ Q^n (Φ X)`: the identity for `n = 0`, and
`θ` at `P^n X` followed by `Q` of the previous one. -/
def powApp : (n : ℕ) → (X : A) → Φ.obj ((standardPow P n).obj X) ⟶ (standardPow Q n).obj (Φ.obj X)
  | 0, _ => 𝟙 _
  | n + 1, X => t.θ.app ((standardPow P n).obj X) ≫ Q.map (powApp n X)

lemma powApp_zero (X : A) : t.powApp 0 X = 𝟙 (Φ.obj X) :=
  rfl

lemma powApp_succ (n : ℕ) (X : A) :
    t.powApp (n + 1) X = t.θ.app ((standardPow P n).obj X) ≫ Q.map (t.powApp n X) :=
  rfl

lemma powApp_one_comp (X : A) : t.powApp 1 X ≫ η.app (Φ.obj X) = Φ.map (ε.app X) := by
  change (t.θ.app X ≫ Q.map (𝟙 _)) ≫ η.app (Φ.obj X) = _
  rw [Q.map_id]
  exact (congrArg (· ≫ η.app (Φ.obj X)) (Category.comp_id (t.θ.app X))).trans (t.θ_comp_η X)

lemma powApp_naturality (n : ℕ) {X Y : A} (f : X ⟶ Y) :
    Φ.map ((standardPow P n).map f) ≫ t.powApp n Y =
      t.powApp n X ≫ (standardPow Q n).map (Φ.map f) := by
  induction n with
  | zero =>
    change Φ.map f ≫ 𝟙 _ = 𝟙 _ ≫ Φ.map f
    rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
    have h := t.θ.naturality ((standardPow P n).map f)
    rw [Functor.comp_map, Functor.comp_map] at h
    change Φ.map (P.map ((standardPow P n).map f)) ≫ t.θ.app _ ≫ Q.map (t.powApp n Y) =
      (t.θ.app _ ≫ Q.map (t.powApp n X)) ≫ Q.map ((standardPow Q n).map (Φ.map f))
    rw [← Category.assoc, h, Category.assoc, Category.assoc, ← Q.map_comp, ← Q.map_comp, ih]

/-- The iterated comparisons as a natural transformation `P^n ⋙ Φ ⟶ Φ ⋙ Q^n`. -/
@[simps]
def pow (n : ℕ) : standardPow P n ⋙ Φ ⟶ Φ ⋙ standardPow Q n where
  app X := t.powApp n X
  naturality _ _ f := t.powApp_naturality n f

variable [Abelian A] [Abelian B] [Φ.Additive]

/-- The iterated comparisons commute with the differentials of the standard resolutions. -/
theorem map_differential_comp_powApp (n : ℕ) (X : A) :
    Φ.map ((standardDifferential P ε n).app X) ≫ t.powApp n X =
      t.powApp (n + 1) X ≫ (standardDifferential Q η n).app (Φ.obj X) := by
  induction n with
  | zero =>
    change Φ.map (ε.app X) ≫ 𝟙 _ = t.powApp 1 X ≫ η.app (Φ.obj X)
    rw [Category.comp_id, t.powApp_one_comp]
  | succ n ih =>
    rw [standardDifferential_succ, standardDifferential_succ, NatTrans.app_sub, NatTrans.app_sub,
      Φ.map_sub, Preadditive.sub_comp, Preadditive.comp_sub]
    congr 1
    · change Φ.map (ε.app ((standardPow P (n + 1)).obj X)) ≫ t.powApp (n + 1) X =
        (t.θ.app ((standardPow P (n + 1)).obj X) ≫ Q.map (t.powApp (n + 1) X)) ≫
          η.app ((standardPow Q (n + 1)).obj (Φ.obj X))
      rw [← t.θ_comp_η, Category.assoc, Category.assoc]
      exact congrArg (t.θ.app _ ≫ ·) (η.naturality (t.powApp (n + 1) X)).symm
    · have h := t.θ.naturality ((standardDifferential P ε n).app X)
      rw [Functor.comp_map, Functor.comp_map] at h
      change Φ.map (P.map ((standardDifferential P ε n).app X)) ≫ t.θ.app _ ≫
          Q.map (t.powApp n X) =
        (t.θ.app ((standardPow P (n + 1)).obj X) ≫ Q.map (t.powApp (n + 1) X)) ≫
          Q.map ((standardDifferential Q η n).app (Φ.obj X))
      rw [← Category.assoc, h, Category.assoc, Category.assoc, ← Q.map_comp, ← Q.map_comp, ih]

section Resolution

variable [P.PreservesZeroMorphisms] [Q.PreservesZeroMorphisms]

/-- The map of standard resolutions along `Φ`: in degree `r`, the comparison
`Φ (P^(r+1) X) ⟶ Q^(r+1) (Φ X)`. -/
@[simps]
def resolution :
    standardResolution P ε ⋙ Φ.mapHomologicalComplex (ComplexShape.down ℕ) ⟶
      Φ ⋙ standardResolution Q η where
  app X :=
    { f := fun r => t.powApp (r + 1) X
      comm' := by
        intro i j hij
        obtain rfl : j + 1 = i := hij
        change t.powApp (j + 1 + 1) X ≫ ((standardResolution Q η).obj (Φ.obj X)).d (j + 1) j =
          Φ.map (((standardResolution P ε).obj X).d (j + 1) j) ≫ t.powApp (j + 1) X
        rw [standardResolution_obj_d, standardResolution_obj_d]
        exact (t.map_differential_comp_powApp (j + 1) X).symm }
  naturality _ _ f := by
    ext r
    exact t.powApp_naturality (r + 1) f

/-- In degree `0`, the map of standard resolutions is compatible with the augmentations. -/
lemma resolution_app_f_zero_comp (X : A) :
    (t.resolution.app X).f 0 ≫ η.app (Φ.obj X) = Φ.map (ε.app X) :=
  t.powApp_one_comp X

end Resolution

section Total

variable [P.Additive] [Q.Additive] (N : ℕ) (L : CochainComplex A ℕ)

/-- `t.powApp (r + 1)` on the summand `(q, r)` of `standardRows`, typed with the two double
complexes: the comparison `Φ (P^(r+1) L^q) ⟶ Q^(r+1) (Φ L^q)`. -/
def rowθ (q : Fin N) (r : ℕ) :
    Φ.obj (((standardRows N P ε L).X q).X r) ⟶
      ((standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).X q).X r :=
  t.powApp (r + 1) (L.X q)

lemma rowθ_naturality (q q' : Fin N) (r : ℕ) :
    Φ.map (((standardRows N P ε L).d q q').f r) ≫ t.rowθ N L q' r =
      t.rowθ N L q r ≫
        ((standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).d q q').f r :=
  t.powApp_naturality (r + 1) (L.d q q')

lemma rowθ_d (q : Fin N) (r : ℕ) :
    Φ.map (((standardRows N P ε L).X q).d (r + 1) r) ≫ t.rowθ N L q r =
      t.rowθ N L q (r + 1) ≫
        ((standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).X q).d
          (r + 1) r := by
  have h₁ : ((standardRows N P ε L).X q).d (r + 1) r =
      (standardDifferential P ε (r + 1)).app (L.X q) :=
    standardResolution_obj_d P ε (L.X q) r
  have h₂ : ((standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).X q).d
      (r + 1) r = (standardDifferential Q η (r + 1)).app (Φ.obj (L.X q)) :=
    standardResolution_obj_d Q η (Φ.obj (L.X q)) r
  rw [h₁, h₂]
  exact t.map_differential_comp_powApp (r + 1) (L.X q)

lemma rowθ_comp_augmentation (q : Fin N) :
    t.rowθ N L q 0 ≫ standardRowsAugmentationApp N Q η
        ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) q 0 =
      Φ.map (standardRowsAugmentationApp N P ε L q 0) :=
  (congrArg (t.rowθ N L q 0 ≫ ·)
    (StandardContraction.augmentation_app_f_zero (P := Q) (ε := η) (Φ.obj (L.X q)))).trans
    ((t.powApp_one_comp (L.X q)).trans
      (congrArg Φ.map (StandardContraction.augmentation_app_f_zero (P := P) (ε := ε) (L.X q))).symm)

variable [PreservesFiniteColimits Φ]

/-- Degree `n` of the comparison of total complexes: on the summand `(q, r)`, `t.powApp (r + 1)`
followed by the inclusion of the summand `(q, r)`. -/
def totalMapF (n : ℤ) :
    Φ.obj (((standardRows N P ε L).total (ComplexShape.up ℤ)).X n) ⟶
      ((standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).total
        (ComplexShape.up ℤ)).X n :=
  totalMapDesc (fun q r h => t.rowθ N L q r ≫
    (standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).ιTotal
      (ComplexShape.up ℤ) q r n h)

@[reassoc]
lemma map_ιTotal_totalMapF (n : ℤ) (q : Fin N) (r : ℕ)
    (h : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = n) :
    Φ.map ((standardRows N P ε L).ιTotal (ComplexShape.up ℤ) q r n h) ≫ t.totalMapF N L n =
      t.rowθ N L q r ≫
        (standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).ιTotal
          (ComplexShape.up ℤ) q r n h :=
  map_ιTotal_totalMapDesc _ q r h

/-- The comparison commutes with the differentials: on the row part by naturality of the
comparisons, on the column part by `map_differential_comp_powApp`. -/
lemma totalMapF_comm (n n' : ℤ) (hnn' : (ComplexShape.up ℤ).Rel n n') :
    t.totalMapF N L n ≫
        ((standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).total
          (ComplexShape.up ℤ)).d n n' =
      Φ.map (((standardRows N P ε L).total (ComplexShape.up ℤ)).d n n') ≫
        t.totalMapF N L n' := by
  have hnn'' : n + 1 = n' := hnn'
  refine totalMap_hom_ext fun q r h => ?_
  rw [map_ιTotal_totalMapF_assoc, ιTotal_standardRows_d, ← Φ.map_comp_assoc,
    ιTotal_standardRows_d, Φ.map_add, Preadditive.add_comp, Preadditive.comp_add]
  congr 1
  · by_cases hqN : (q : ℕ) + 1 < N
    · have hrel : (upFin N).Rel q ⟨(q : ℕ) + 1, hqN⟩ := rfl
      have hπ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ)
          (⟨(q : ℕ) + 1, hqN⟩, r) = n' := by
        rw [upFin_π] at h ⊢
        push_cast
        omega
      have hε : ComplexShape.ε₁ (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) = 1 :=
        rfl
      rw [standardRowsD₁_eq _ _ _ _ hrel r n' hπ, standardRowsD₁_eq _ _ _ _ hrel r n' hπ, hε,
        one_smul, one_smul, Φ.map_comp, Category.assoc, map_ιTotal_totalMapF, ← Category.assoc,
        ← Category.assoc, t.rowθ_naturality]
    · have hnext : ¬ (upFin N).Rel q ((upFin N).next q) := fun hr => by
        have hr' : (q : ℕ) + 1 = ((upFin N).next q : ℕ) := hr
        have := ((upFin N).next q).isLt
        omega
      rw [standardRowsD₁_eq_zero _ _ _ _ _ _ _ hnext, standardRowsD₁_eq_zero _ _ _ _ _ _ _ hnext,
        Φ.map_zero, zero_comp, comp_zero]
  · cases r with
    | zero => rw [standardRowsD₂_zero, standardRowsD₂_zero, Φ.map_zero, zero_comp, comp_zero]
    | succ r =>
      have hrel : (ComplexShape.down ℕ).Rel (r + 1) r := rfl
      have hπ : ComplexShape.π (upFin N) (ComplexShape.down ℕ) (ComplexShape.up ℤ) (q, r) =
          n' := by
        rw [upFin_π] at h ⊢
        push_cast at h ⊢
        omega
      rw [standardRowsD₂_eq _ _ _ _ q hrel n' hπ, standardRowsD₂_eq _ _ _ _ q hrel n' hπ,
        Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul, Φ.map_comp,
        Category.assoc, map_ιTotal_totalMapF, ← Category.assoc, ← Category.assoc, t.rowθ_d]

/-- The comparison `Φ (Tot (standardRows N P ε L)) ⟶ Tot (standardRows N Q η (Φ L))` of total
complexes (rows `q < N`), given on the summand `(q, r)` by `t.powApp (r + 1)`. -/
def totalMap :
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((standardRows N P ε L).total (ComplexShape.up ℤ)) ⟶
      (standardRows N Q η ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).total
        (ComplexShape.up ℤ) where
  f n := t.totalMapF N L n
  comm' n n' h := t.totalMapF_comm N L n n' h

lemma totalMap_f (n : ℤ) : (t.totalMap N L).f n = t.totalMapF N L n :=
  rfl

variable {L} in
/-- The comparison of total complexes is natural in `L`. -/
lemma totalMapF_naturality {L' : CochainComplex A ℕ} (f : L ⟶ L') (n : ℤ) :
    Φ.map ((HomologicalComplex₂.total.map (((upFinEmbedding N).restrictionFunctor _).map
        (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).map f))
          (ComplexShape.up ℤ)).f n) ≫ t.totalMapF N L' n =
      t.totalMapF N L n ≫
        (HomologicalComplex₂.total.map (((upFinEmbedding N).restrictionFunctor _).map
          (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map
            ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map f))) (ComplexShape.up ℤ)).f n := by
  refine totalMap_hom_ext fun q r h => ?_
  have hmap := HomologicalComplex₂.ιTotal_map _ _
    (((upFinEmbedding N).restrictionFunctor _).map
      (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).map f))
    (ComplexShape.up ℤ) q r n h
  have hmap' := HomologicalComplex₂.ιTotal_map _ _
    (((upFinEmbedding N).restrictionFunctor _).map
      (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)))
    (ComplexShape.up ℤ) q r n h
  rw [← Φ.map_comp_assoc, hmap, Φ.map_comp, Category.assoc, map_ιTotal_totalMapF,
    map_ιTotal_totalMapF_assoc, hmap', ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ _) (t.powApp_naturality (r + 1) (f.f q))

/-- Followed by the totalized augmentation and the comparison with the extension of `Φ L` to
`ℤ`, the comparison of total complexes is `Φ` of the corresponding composite for `L`, followed
by the identification `DerivedPlus.mapExtendIso` of the two extensions. -/
lemma totalMapF_comp_columnComparisonF (n : ℤ) :
    t.totalMapF N L n ≫ (standardRowsAugmentation N Q η
        ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)).f n ≫
          columnComparisonF N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) n =
      Φ.map ((standardRowsAugmentation N P ε L).f n ≫ columnComparisonF N L n) ≫
        (DerivedPlus.mapExtendIso Φ L ComplexShape.embeddingUpNat).inv.f n := by
  refine totalMap_hom_ext fun q r h => ?_
  rw [map_ιTotal_totalMapF_assoc, ← Φ.map_comp_assoc, ιTotal_standardRowsAugmentation_assoc,
    ιTotal_standardRowsAugmentation_assoc, ιTotal_columnComparisonF, ιTotal_columnComparisonF]
  cases r with
  | succ r =>
    have h₁ : standardRowsAugmentationApp N Q η
        ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) q (r + 1) ≫
          columnSummand N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) n q (r + 1) h =
        0 :=
      comp_zero
    have h₂ : standardRowsAugmentationApp N P ε L q (r + 1) ≫ columnSummand N L n q (r + 1) h = 0 :=
      comp_zero
    rw [h₁, h₂, comp_zero, Φ.map_zero, zero_comp]
  | zero =>
    have hq : ((q : ℕ) : ℤ) = n := by
      have h' : ((q : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = n := h
      simpa using h'
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ columnSummand N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) n
      q 0 h) (t.rowθ_comp_augmentation N L q)).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ (DerivedPlus.mapExtendIso Φ L
      ComplexShape.embeddingUpNat).inv.f n) (Φ.map_comp _ _)).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (Φ.map (standardRowsAugmentationApp N P ε L q 0) ≫ ·)
      (map_extendXIso_inv_comp Φ L
        (ComplexShape.embeddingUpNat.r_eq_some (i := (q : ℕ)) (by simpa using hq))).symm

variable {L} in
/-- `totalMap` is natural in `L`, written with `upFinTotalFunctor`. -/
lemma totalMap_naturality {L' : CochainComplex A ℕ} (f : L ⟶ L') :
    (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map ((upFinTotalFunctor A N).map
        (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).map f)) ≫
      t.totalMap N L' =
    t.totalMap N L ≫ (upFinTotalFunctor B N).map
      (((standardResolution Q η).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map f)) :=
  HomologicalComplex.hom_ext _ _ fun n => t.totalMapF_naturality N f n

/-- For `L` vanishing in degrees `q ≥ N`: `totalMap` followed by the morphism to `Φ L` extended
to `ℤ` (totalized augmentation, then `columnComparison`) is `Φ` of the corresponding morphism
for `L`, followed by the identification `DerivedPlus.mapExtendIso` of the two extensions. -/
lemma totalMap_comp_toExtend (hL : ∀ q, N ≤ q → IsZero (L.X q)) :
    t.totalMap N L ≫ standardRowsAugmentation N Q η
        ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) ≫
          columnComparison N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
            (fun q hq => Φ.map_isZero (hL q hq)) =
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (standardRowsAugmentation N P ε L ≫ columnComparison N L hL) ≫
        (DerivedPlus.mapExtendIso Φ L ComplexShape.embeddingUpNat).inv :=
  HomologicalComplex.hom_ext _ _ fun n => t.totalMapF_comp_columnComparisonF N L n

/-- If the totalized augmentations of `L` and of `Φ L` are quasi-isomorphisms and `L` vanishes
in degrees `q ≥ N`, then `totalMap` is a quasi-isomorphism (`Φ` exact). -/
theorem quasiIso_totalMap [PreservesFiniteLimits Φ] (hL : ∀ q, N ≤ q → IsZero (L.X q))
    (hP : QuasiIso (standardRowsAugmentation N P ε L))
    (hQ : QuasiIso (standardRowsAugmentation N Q η
      ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L))) :
    QuasiIso (t.totalMap N L) := by
  have : Φ.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels Φ
  have : IsIso (columnComparison N L hL) := isIso_columnComparison N L hL
  have : IsIso (columnComparison N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
      (fun q hq => Φ.map_isZero (hL q hq))) :=
    isIso_columnComparison N _ _
  have hc₁ : QuasiIso (columnComparison N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
      (fun q hq => Φ.map_isZero (hL q hq))) :=
    inferInstance
  have hc₂ : QuasiIso (columnComparison N L hL) := inferInstance
  have h₁ : QuasiIso (standardRowsAugmentation N Q η
      ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) ≫
        columnComparison N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
          (fun q hq => Φ.map_isZero (hL q hq))) :=
    quasiIso_comp _ _ (hφ := hQ) (hφ' := hc₁)
  have h₂ : QuasiIso (standardRowsAugmentation N P ε L ≫ columnComparison N L hL) :=
    quasiIso_comp _ _ (hφ := hP) (hφ' := hc₂)
  have h₃ : QuasiIso ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (standardRowsAugmentation N P ε L ≫ columnComparison N L hL)) :=
    inferInstance
  have h₄ : QuasiIso (t.totalMap N L ≫ standardRowsAugmentation N Q η
      ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L) ≫
        columnComparison N ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj L)
          (fun q hq => Φ.map_isZero (hL q hq))) := by
    rw [t.totalMap_comp_toExtend N L hL]
    infer_instance
  exact quasiIso_of_comp_right _ _ (hφ := h₁) (hφφ' := h₄)

end Total

section System

variable [P.Additive] [Q.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] {ℓ : ℕ} (N : ℕ) (K : DivisibleSystem (CochainComplex A ℕ) ℓ)

/-- The morphism of `ℓ`-divisible systems from `Φ` of the total complexes of the standard
resolutions along `P` of `K` to the total complexes of the standard resolutions along `Q` of
`Φ K` (rows `q < N`): `totalMap` at every level. -/
def standardTotalSystemMap :
    (K.standardTotalSystem N P ε).map (Φ.mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (K.map (Φ.mapHomologicalComplex (ComplexShape.up ℕ))).standardTotalSystem N Q η :=
  ⟨{ app := fun m => t.totalMap N (K.tower.obj m)
     naturality := fun _ _ φ => t.totalMap_naturality N (K.tower.map φ) },
    fun h => t.totalMap_naturality N (K.inclusion h)⟩

lemma standardTotalSystemMap_tower_app (m : ℕ) :
    (t.standardTotalSystemMap N K).tower.app (op m) = t.totalMap N (K.obj m) :=
  rfl

/-- For `K` vanishing in degrees `q ≥ N`: `standardTotalSystemMap` followed by the morphism to
`Φ K` extended to `ℤ` is `Φ` of the morphism for `K`, followed by `DerivedPlus.mapExtendIso`. -/
lemma standardTotalSystemMap_tower_app_comp (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q))
    (m : ℕ) :
    (t.standardTotalSystemMap N K).tower.app (op m) ≫
        ((K.map (Φ.mapHomologicalComplex (ComplexShape.up ℕ))).standardTotalSystemToExtend N Q η
          (fun m q hq => Φ.map_isZero (hK m q hq))).tower.app (op m) =
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((K.standardTotalSystemToExtend N P ε hK).tower.app (op m)) ≫
        (DerivedPlus.mapExtendIso Φ (K.obj m) ComplexShape.embeddingUpNat).inv :=
  t.totalMap_comp_toExtend N (K.obj m) (hK m)

/-- Given contractions for `P` and `Q` (`StandardContraction`), each level of
`standardTotalSystemMap` is a quasi-isomorphism, for `K` vanishing in degrees `q ≥ N`. -/
theorem quasiIso_standardTotalSystemMap_tower_app {A₁ : Type*} [Category* A₁] [Abelian A₁]
    {B₁ : Type*} [Category* B₁] [Abelian B₁] {F : A ⥤ A₁} {F' : B ⥤ B₁} [F.Additive] [F.Faithful]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F'.Additive] [F'.Faithful]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (c : StandardContraction F P ε)
    (c' : StandardContraction F' Q η) (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ) :
    QuasiIso ((t.standardTotalSystemMap N K).tower.app (op m)) :=
  t.quasiIso_totalMap N (K.obj m) (hK m) (c.quasiIso_standardRowsAugmentation N (K.obj m))
    (c'.quasiIso_standardRowsAugmentation N _)

end System

end StandardMap

end StandardMap

section Group

open Representation

variable (k : Type u) [CommRing k] {Γ Γ' : Type v} [Group Γ] [Group Γ'] [Fintype Γ']
  [DecidableEq Γ] (π : Γ' →* Γ)

/-- The `k`-linear normalized fiber sum `⟦γ ⊗ v⟧ ↦ c • ∑_{π γ' = γ} ⟦γ' ⊗ v⟧` from
`Ind_1^Γ Res_1^Γ V` to `Ind_1^Γ' Res_1^Γ' (Res_π V)`, where `c` is the inverse of `|ker π|` in `k`
(`Ring.inverse`, which is `0` when `|ker π|` is not a unit). -/
def fiberAverageLinear (V : Rep.{max w u v} k Γ) :
    IndV (⊥ : Subgroup Γ).subtype (V.ρ.comp (⊥ : Subgroup Γ).subtype) →ₗ[k]
      IndV (⊥ : Subgroup Γ').subtype ((V.ρ.comp π).comp (⊥ : Subgroup Γ').subtype) :=
  Coinvariants.lift _ (TensorProduct.lift <| (Finsupp.lift _ k Γ fun γ =>
      Ring.inverse (Nat.card π.ker : k) • ∑ γ' ∈ Finset.univ.filter (π · = γ),
        IndV.mk (⊥ : Subgroup Γ').subtype ((V.ρ.comp π).comp (⊥ : Subgroup Γ').subtype) γ') ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap) fun g => by
    rw [Subsingleton.elim g 1, map_one]
    exact LinearMap.comp_id _

lemma fiberAverageLinear_mk (V : Rep.{max w u v} k Γ) (γ : Γ) (x : V) :
    fiberAverageLinear k π V (IndV.mk _ _ γ x) =
      Ring.inverse (Nat.card π.ker : k) • ∑ γ' ∈ Finset.univ.filter (π · = γ),
        IndV.mk (⊥ : Subgroup Γ').subtype ((V.ρ.comp π).comp (⊥ : Subgroup Γ').subtype) γ' x := by
  simp [fiberAverageLinear]

/-- The fiber sum intertwines the action of `π g` on `Ind_1^Γ Res_1^Γ V` with the action of `g`
on `Ind_1^Γ' Res_1^Γ' (Res_π V)`: right multiplication by `g⁻¹` permutes the fibers of `π`. -/
lemma fiberAverageLinear_comm (V : Rep.{max w u v} k Γ) (g : Γ') :
    fiberAverageLinear k π V ∘ₗ ind (⊥ : Subgroup Γ).subtype (V.ρ.comp (⊥ : Subgroup Γ).subtype)
        (π g) =
      ind (⊥ : Subgroup Γ').subtype ((V.ρ.comp π).comp (⊥ : Subgroup Γ').subtype) g ∘ₗ
        fiberAverageLinear k π V := by
  refine IndV.hom_ext _ _ fun γ => LinearMap.ext fun x => ?_
  change fiberAverageLinear k π V (ind _ _ (π g) (IndV.mk _ _ γ x)) =
    ind _ _ g (fiberAverageLinear k π V (IndV.mk _ _ γ x))
  rw [ind_mk, fiberAverageLinear_mk, fiberAverageLinear_mk, map_smul, map_sum]
  simp only [ind_mk]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine (Fintype.sum_equiv (Equiv.mulRight g⁻¹) _ _ fun γ' => ?_).symm
  simp only [Equiv.coe_mulRight, map_mul, map_inv, mul_left_inj]

omit [DecidableEq Γ] in
/-- The counit `Ind_1^Γ Res_1^Γ V ⟶ V` sends `⟦γ ⊗ v⟧` to `γ⁻¹ v`. -/
lemma indResBotCounit_app_mk (V : Rep.{max w u v} k Γ) (γ : Γ) (x : V) :
    ((indResBotCounit.{w} k Γ).app V).hom
        (IndV.mk (⊥ : Subgroup Γ).subtype (V.ρ.comp (⊥ : Subgroup Γ).subtype) γ x) =
      V.ρ γ⁻¹ x := by
  have h : (indResBotCounit.{w} k Γ).app V =
      ((Rep.indResAdjunction.{max w u v} k (⊥ : Subgroup Γ).subtype).homEquiv _ V).symm
        (𝟙 _) := by
    rw [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h]
  change ((Rep.indResHomEquiv (⊥ : Subgroup Γ).subtype _ V).symm (𝟙 _)).hom
    (IndV.mk (⊥ : Subgroup Γ).subtype (V.ρ.comp (⊥ : Subgroup Γ).subtype) γ x) = _
  simp

/-- The normalized fiber sum as a natural transformation
`Ind_1^Γ Res_1^Γ ⋙ Res_π ⟶ Res_π ⋙ Ind_1^Γ' Res_1^Γ'`. -/
def fiberAverage :
    indResBot.{w} k Γ ⋙ Rep.resFunctor π ⟶ Rep.resFunctor π ⋙ indResBot.{w} k Γ' where
  app V := Rep.ofHom ⟨fiberAverageLinear k π V, fiberAverageLinear_comm k π V⟩
  naturality V W f := by
    refine Rep.hom_ext <| IntertwiningMap.ext <| IndV.hom_ext _ _ fun γ => LinearMap.ext fun x => ?_
    change fiberAverageLinear k π W (IndV.mk _ _ γ (f.hom x)) =
      ((Rep.indFunctor k (⊥ : Subgroup Γ').subtype).map ((Rep.resFunctor _).map
        ((Rep.resFunctor π).map f))).hom (fiberAverageLinear k π V (IndV.mk _ _ γ x))
    rw [fiberAverageLinear_mk, fiberAverageLinear_mk, map_smul, map_sum]
    simp [Rep.indMap]

lemma fiberAverage_app_mk (V : Rep.{max w u v} k Γ) (γ : Γ) (x : V) :
    ((fiberAverage.{w} k π).app V).hom
        (IndV.mk (⊥ : Subgroup Γ).subtype (V.ρ.comp (⊥ : Subgroup Γ).subtype) γ x) =
      Ring.inverse (Nat.card π.ker : k) • ∑ γ' ∈ Finset.univ.filter (π · = γ),
        IndV.mk (⊥ : Subgroup Γ').subtype ((V.ρ.comp π).comp (⊥ : Subgroup Γ').subtype) γ' x :=
  fiberAverageLinear_mk k π V γ x

/-- For `π` surjective, every fiber of `π` has `|ker π|` elements. -/
lemma card_filter_eq_nat_card_ker (hπ : Function.Surjective π) (γ : Γ) :
    (Finset.univ.filter (π · = γ)).card = Nat.card π.ker := by
  rw [MonoidHom.card_fiber_eq_of_mem_range π (hπ γ) (hπ 1), ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => π.mem_ker.symm)

/-- For `π` surjective with `|ker π|` invertible in `k`, the normalized fiber sum is a map of
augmented functors along `Res_π` from `Ind_1^Γ Res_1^Γ` to `Ind_1^Γ' Res_1^Γ'`. -/
def groupStandardMap (hπ : Function.Surjective π) (hk : IsUnit (Nat.card π.ker : k)) :
    StandardMap (Rep.resFunctor π) (indResBot.{w} k Γ) (indResBotCounit.{w} k Γ)
      (indResBot.{w} k Γ') (indResBotCounit.{w} k Γ') where
  θ := fiberAverage.{w} k π
  θ_comp_η V := by
    refine Rep.hom_ext <| IntertwiningMap.ext <| IndV.hom_ext _ _ fun γ => LinearMap.ext fun x => ?_
    change ((indResBotCounit.{w} k Γ').app ((Rep.resFunctor π).obj V)).hom
        (((fiberAverage.{w} k π).app V).hom (IndV.mk _ _ γ x)) =
      ((indResBotCounit.{w} k Γ).app V).hom (IndV.mk _ _ γ x)
    rw [fiberAverage_app_mk, map_smul, map_sum]
    simp only [indResBotCounit_app_mk]
    have h : ∀ γ' ∈ Finset.univ.filter (π · = γ),
        ((indResBotCounit.{w} k Γ').app ((Rep.resFunctor π).obj V)).hom
          (IndV.mk (⊥ : Subgroup Γ').subtype ((V.ρ.comp π).comp (⊥ : Subgroup Γ').subtype) γ' x) =
        V.ρ γ⁻¹ x := fun γ' hγ' => by
      rw [Finset.mem_filter] at hγ'
      refine (indResBotCounit_app_mk.{w} k ((Rep.resFunctor π).obj V) γ' x).trans ?_
      change V.ρ (π γ'⁻¹) x = _
      rw [map_inv, hγ'.2]
    refine (congrArg (Ring.inverse (Nat.card π.ker : k) • ·) (Finset.sum_congr rfl h)).trans ?_
    rw [Finset.sum_const, card_filter_eq_nat_card_ker π hπ, ← Nat.cast_smul_eq_nsmul k, smul_smul,
      Ring.inverse_mul_cancel _ hk, one_smul]

end Group

namespace DivisibleSystem

section GroupSystem

variable {k : Type u} [CommRing k] {Γ Γ' : Type v} [Group Γ] [Group Γ'] [Finite Γ] [Fintype Γ']
  [DecidableEq Γ] (π : Γ' →* Γ) (hπ : Function.Surjective π) (hk : IsUnit (Nat.card π.ker : k))
  {ℓ : ℕ} (N : ℕ) (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ)

/-- `standardTotalSystemMap` for the normalized fiber sum `groupStandardMap`: the morphism from
`Res_π` of the total complexes of the standard resolutions along `Ind_1^Γ Res_1^Γ` of `K` to those
along `Ind_1^Γ' Res_1^Γ'` of `Res_π K`. -/
abbrev groupStandardTotalSystemMap :
    (K.groupStandardTotalSystem N).map
        ((Rep.resFunctor.{max w u v} (k := k) π).mapHomologicalComplex (ComplexShape.up ℤ)) ⟶
      (K.map ((Rep.resFunctor.{max w u v} (k := k) π).mapHomologicalComplex
        (ComplexShape.up ℕ))).groupStandardTotalSystem N :=
  (groupStandardMap.{w} k π hπ hk).standardTotalSystemMap N K

/-- `standardTotalSystemMap_tower_app_comp` for `groupStandardTotalSystemMap`. -/
lemma groupStandardTotalSystemMap_tower_app_comp (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q))
    (m : ℕ) :
    (groupStandardTotalSystemMap.{w} π hπ hk N K).tower.app (op m) ≫
        (groupStandardTotalSystemToExtend.{w} N
          (K.map ((Rep.resFunctor.{max w u v} (k := k) π).mapHomologicalComplex
            (ComplexShape.up ℕ)))
          (fun m q hq => (Rep.resFunctor π).map_isZero (hK m q hq))).tower.app (op m) =
      ((Rep.resFunctor.{max w u v} (k := k) π).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((groupStandardTotalSystemToExtend.{w} N K hK).tower.app (op m)) ≫
        (DerivedPlus.mapExtendIso (Rep.resFunctor π) (K.obj m) ComplexShape.embeddingUpNat).inv :=
  (groupStandardMap.{w} k π hπ hk).standardTotalSystemMap_tower_app_comp N K hK m

/-- Each level of `groupStandardTotalSystemMap` is a quasi-isomorphism, for `K` vanishing in
degrees `q ≥ N`. -/
theorem quasiIso_groupStandardTotalSystemMap_tower_app
    (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ) :
    QuasiIso ((groupStandardTotalSystemMap.{w} π hπ hk N K).tower.app (op m)) :=
  (groupStandardMap.{w} k π hπ hk).quasiIso_standardTotalSystemMap_tower_app N K
    (indResBotContraction.{w} k Γ) (indResBotContraction.{w} k Γ') hK m

end GroupSystem

end DivisibleSystem

end Langlands.Cohomology
