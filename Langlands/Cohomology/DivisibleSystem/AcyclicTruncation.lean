import Langlands.Cohomology.DivisibleSystem.Sections
import Langlands.Cohomology.AcyclicResolution.Comparison
import Langlands.Cohomology.AcyclicResolution.ComparisonProof

/-!
# Acyclic truncated resolutions of `ℓ`-divisible systems

Harris 1999, §2, pp.304–305: the resolutions `F_m^•` of Lemma 2.2 are `RΓ_c`-acyclic; by
Fact 2 (`H^q_c` vanishes in degrees `q > D`) the truncations `G_m^• = τ_{≤ D+1}(F_m^•)` are
again `RΓ_c`-acyclic resolutions of finite length (Lemma 2.2 bis), Harris checks that compact
sections of the projections of `G^q` are surjective, and (2.3) identifies `H^q_c` with the
cohomology of the complexes of sections `G_m^•(U(ẽ)_F̄)`.

This module proves the generic form of these steps for an exact endofunctor `F` of an abelian
category `C` with enough injectives, a monic coaugmentation `η : 𝟭 C ⟶ F`, an `ℓ`-divisible
system `T` and an additive left exact functor `Φ : C ⥤ E` in place of compact sections:

* `resolutionSystemAugmentation` and `truncatedResolutionAugmentation` are the augmentations
  `T m ⟶ F_m^•` and `T m ⟶ G_m^•` of level `m`, both quasi-isomorphisms; the second factors
  the first through the inclusion of the truncation.
* Assuming that the higher right derived functors of `Φ` vanish on every `F(M)` (Harris's
  `F(T)` is `RΓ_c`-acyclic) and on every `T m` in degrees above `D` (the form of Fact 2 used),
  `isZero_rightDerived_residualSystem_obj` shows that they vanish on the residual systems
  `R q` in degrees `n > 0` with `n + q > D`, by dimension shifting; in particular `R (D + 1)`
  is `Φ`-acyclic and every term of every level of the truncated resolution system is
  `Φ`-acyclic (`isZero_rightDerived_truncatedResolutionSystem_obj_X`).
* `epi_map_projection_of_isZero_rightDerived_one`: if `R^1 Φ` vanishes on every level of an
  `ℓ`-divisible system, `Φ` maps its projections to epimorphisms. This gives the hypotheses of
  the published `truncatedResolutionSectionsSystem`, and `acyclicTruncatedSectionsSystem` is
  the resulting `ℓ`-divisible system of finite-length complexes `Φ(G_m^•)`.
* `acyclicTruncatedSectionsHomologyIso` is (2.3): `Hⁿ(Φ(G_m^•)) ≅ Rⁿ Φ(T m)`, the published
  comparison map of an acyclic resolution (`AcyclicResolution.resolutionComparison`), which is
  an isomorphism by the published `acyclicResolutionComparisonStatement`. Both sides vanish for
  `n > D`.

The exactness of `F`, the acyclicity of `F(M)` and the vanishing on `T m` are hypotheses; the
instance for Harris's sheaves is not treated here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

namespace DivisibleSystem

section Augmentation

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ) (D : ℕ)

/-- The augmentation `T m ⟶ F_m^•` of level `m` of the resolution system: the coaugmentation
`T m ⟶ F^0_m` in degree zero. -/
def resolutionSystemAugmentation (m : ℕ) :
    (CochainComplex.single₀ C).obj (T.obj m) ⟶ (T.resolutionSystem F η).obj m :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(T.residualInclusion F η 0).tower.app (op m), by
      rw [resolutionSystem_obj_d]
      exact T.residualInclusion_termDifferential_tower_app F η 0 (op m)⟩

lemma resolutionSystemAugmentation_f_zero (m : ℕ) :
    (T.resolutionSystemAugmentation F η m).f 0 = (T.residualInclusion F η 0).tower.app (op m) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Level `m` of the resolution system is a resolution of `T m`. -/
instance resolutionSystemAugmentation_quasiIso (m : ℕ) :
    QuasiIso (T.resolutionSystemAugmentation F η m) where
  quasiIsoAt n := by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine ⟨?_, ?_⟩
        · exact shortComplex_exact_congr (T.resolutionSystemAugmentation_f_zero F η m).symm
            (T.resolutionSystem_obj_d F η m 0).symm
            (T.residualInclusion_termDifferential_exact F η 0 m)
        · change Mono ((T.resolutionSystemAugmentation F η m).f 0)
          rw [resolutionSystemAugmentation_f_zero]
          exact T.mono_residualInclusion_tower_app F η 0 (op m)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · exact T.resolutionSystem_obj_exactAt F η m n
      · exact CochainComplex.exactAt_succ_single_obj _ _

/-- In degree zero the inclusion of the truncated resolution is an isomorphism. -/
instance isIso_truncatedResolutionHom_f_zero (m : ℕ) :
    IsIso (((T.truncatedResolutionHom F η D).tower.app (op m)).f 0) :=
  isIso_truncationInclusion_tower_app (T.termSystem F η) D (T.residualSystem F η (D + 1))
    (T.residualInclusion F η (D + 1)) (Nat.zero_le D) (op m)

/-- If `g₀` is an isomorphism, `g₁` is a monomorphism and `g₀ ≫ d = d' ≫ g₁`, then a morphism
`a` killed by `d` gives a morphism `a ≫ g₀⁻¹` killed by `d'`. -/
lemma comp_inv_comp_eq_zero_of_comm {A X Y Z W : C} (a : A ⟶ X) (g₀ : Y ⟶ X) [IsIso g₀]
    (d' : Y ⟶ Z) (g₁ : Z ⟶ W) [Mono g₁] (d : X ⟶ W) (hcomm : g₀ ≫ d = d' ≫ g₁)
    (h : a ≫ d = 0) : (a ≫ inv g₀) ≫ d' = 0 := by
  rw [← cancel_mono g₁, zero_comp]
  simp only [Category.assoc]
  rw [← hcomm, IsIso.inv_hom_id_assoc, h]

/-- The augmentation `T m ⟶ G_m^•` of level `m` of the truncated resolution system. -/
def truncatedResolutionAugmentation (m : ℕ) :
    (CochainComplex.single₀ C).obj (T.obj m) ⟶ (T.truncatedResolutionSystem F η D).obj m :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(T.resolutionSystemAugmentation F η m).f 0 ≫
      inv (((T.truncatedResolutionHom F η D).tower.app (op m)).f 0), by
      have : Mono (((T.truncatedResolutionHom F η D).tower.app (op m)).f 1) :=
        mono_truncationInclusion_tower_app (T.termSystem F η) D (T.residualSystem F η (D + 1))
          (T.residualInclusion F η (D + 1)) 1 (op m)
      have h : (T.resolutionSystemAugmentation F η m).f 0 ≫
          ((T.resolutionSystem F η).obj m).d 0 1 = 0 := by
        rw [resolutionSystemAugmentation_f_zero, resolutionSystem_obj_d]
        exact T.residualInclusion_termDifferential_tower_app F η 0 (op m)
      exact comp_inv_comp_eq_zero_of_comm _ _ _ _ _
        (((T.truncatedResolutionHom F η D).tower.app (op m)).comm 0 1) h⟩

lemma truncatedResolutionAugmentation_f_zero (m : ℕ) :
    (T.truncatedResolutionAugmentation F η D m).f 0 =
      (T.resolutionSystemAugmentation F η m).f 0 ≫
        inv (((T.truncatedResolutionHom F η D).tower.app (op m)).f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation of the truncation followed by the inclusion of the truncation is the
augmentation of the resolution. -/
@[reassoc (attr := simp)]
lemma truncatedResolutionAugmentation_comp (m : ℕ) :
    T.truncatedResolutionAugmentation F η D m ≫ (T.truncatedResolutionHom F η D).tower.app (op m) =
      T.resolutionSystemAugmentation F η m := by
  ext
  rw [HomologicalComplex.comp_f, truncatedResolutionAugmentation_f_zero, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id]

/-- Level `m` of the truncated resolution system is a resolution of `T m` (Harris's
Lemma 2.2 bis without acyclicity). -/
instance truncatedResolutionAugmentation_quasiIso (m : ℕ) :
    QuasiIso (T.truncatedResolutionAugmentation F η D m) := by
  have : QuasiIso (T.truncatedResolutionAugmentation F η D m ≫
      (T.truncatedResolutionHom F η D).tower.app (op m)) := by
    rw [truncatedResolutionAugmentation_comp]
    infer_instance
  exact quasiIso_of_comp_right _ ((T.truncatedResolutionHom F η D).tower.app (op m))

end Augmentation

section Acyclic

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C] {ℓ : ℕ}
  {E : Type u'} [Category.{v'} E] [Abelian E] (Φ : C ⥤ E) [Φ.Additive]

/-- If `R^1 Φ` vanishes on every level of an `ℓ`-divisible system `S`, a left exact `Φ` maps
every projection of `S` to an epimorphism. -/
lemma epi_map_projection_of_isZero_rightDerived_one [PreservesFiniteLimits Φ]
    (S : DivisibleSystem C ℓ) (h : ∀ m, IsZero ((Φ.rightDerived 1).obj (S.obj m)))
    {m' m : ℕ} (hm : m' ≤ m) : Epi (Φ.map (S.projection hm)) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard E
  refine S.epi_map_projection_of_succ Φ (fun k => ?_) hm
  rcases k with _ | k
  · exact (Φ.map_isZero S.isZero_obj_zero).epi _
  · have key := (DerivedPlus.shortExact_map_of_isZero_rightDerived_one Φ
      (S.shortExact (show 1 < k + 2 by omega)) (h 1)).epi_g
    have aux : ∀ (n : ℕ) (hn : n ≤ k + 2), n = k + 2 - 1 → Epi (Φ.map (S.projection hn)) := by
      rintro n hn rfl
      exact key
    exact aux (k + 1) _ (by omega)

variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ) (D : ℕ)
  (hF : ∀ (M : C) (r : ℕ), IsZero ((Φ.rightDerived (r + 1)).obj (F.obj M)))
  (hT : ∀ (m n : ℕ), D < n → IsZero ((Φ.rightDerived n).obj (T.obj m)))

include hF hT in
/-- Dimension shifting along `0 ⟶ R q ⟶ F(R q) ⟶ R (q + 1) ⟶ 0`: if the higher right derived
functors of `Φ` vanish on every `F(M)` and on every `T m` in degrees above `D`, they vanish on
every level of `R q` in degrees `n > 0` with `n + q > D`. -/
lemma isZero_rightDerived_residualSystem_obj (q m n : ℕ) (h : D < n + q) (hn : 0 < n) :
    IsZero ((Φ.rightDerived n).obj ((T.residualSystem F η q).obj m)) := by
  induction q generalizing n with
  | zero => exact hT m n (by omega)
  | succ q ih =>
    let := HasDerivedCategory.standard C
    let := HasDerivedCategory.standard E
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    exact (DerivedPlus.rightDerived_exact₃ Φ (T.residual_shortExact F η q m) (r + 1) (r + 2)
      rfl).isZero_X₂ ((hF ((T.residualSystem F η q).obj m) r).eq_of_src _ _)
      ((ih (r + 2) (by omega) (by omega)).eq_of_tgt _ _)

include hF hT in
/-- Under the hypotheses of `isZero_rightDerived_residualSystem_obj`, the residual system
`R (D + 1)` is `Φ`-acyclic. -/
lemma isZero_rightDerived_residualSystem_succ_obj (m r : ℕ) :
    IsZero ((Φ.rightDerived (r + 1)).obj ((T.residualSystem F η (D + 1)).obj m)) :=
  isZero_rightDerived_residualSystem_obj Φ F η T D hF hT (D + 1) m (r + 1) (by omega)
    (by omega)

include hF hT in
/-- Every term of every level of the truncated resolution system is `Φ`-acyclic. -/
lemma isZero_rightDerived_truncatedResolutionSystem_obj_X (m i r : ℕ) :
    IsZero ((Φ.rightDerived (r + 1)).obj (((T.truncatedResolutionSystem F η D).obj m).X i)) := by
  change IsZero ((Φ.rightDerived (r + 1)).obj
    ((truncationTerm (T.termSystem F η) D (T.residualSystem F η (D + 1)) i).obj m))
  rcases lt_trichotomy i (D + 1) with hi | rfl | hi
  · rw [truncationTerm_of_le _ _ _ (by omega : i ≤ D)]
    exact hF ((T.residualSystem F η i).obj m) r
  · rw [truncationTerm_of_eq _ _ _ rfl]
    exact isZero_rightDerived_residualSystem_succ_obj Φ F η T D hF hT m r
  · exact AcyclicComparison.isZero_rightDerived_obj_of_isZero Φ _
      (isZero_truncationTerm_tower_obj _ _ _ hi (op m))

variable [PreservesFiniteLimits Φ]

include hF in
/-- `Φ` maps the projections of every term system `F^q` to epimorphisms. -/
lemma epi_map_termSystem_projection (q : ℕ) {m' m : ℕ} (hm : m' ≤ m) :
    Epi (Φ.map ((T.termSystem F η q).projection hm)) :=
  epi_map_projection_of_isZero_rightDerived_one Φ _
    (fun m => hF ((T.residualSystem F η q).obj m) 0) hm

include hF hT in
/-- `Φ` maps the projections of the residual system `R (D + 1)` to epimorphisms. -/
lemma epi_map_residualSystem_succ_projection {m' m : ℕ} (hm : m' ≤ m) :
    Epi (Φ.map ((T.residualSystem F η (D + 1)).projection hm)) :=
  epi_map_projection_of_isZero_rightDerived_one Φ _
    (fun m => isZero_rightDerived_residualSystem_succ_obj Φ F η T D hF hT m 0) hm

/-- Harris's `ℓ`-divisible system of finite-length complexes `Φ(G_m^•)` (p.305), for an
`F` whose values are `Φ`-acyclic and a system `T` whose levels have no higher `Φ`-cohomology
above degree `D`. -/
def acyclicTruncatedSectionsSystem : DivisibleSystem (CochainComplex E ℕ) ℓ :=
  T.truncatedResolutionSectionsSystem F η D Φ
    (fun q _ _ _ hm => epi_map_termSystem_projection Φ F η T hF q hm)
    (fun hm => epi_map_residualSystem_succ_projection Φ F η T D hF hT hm)

lemma acyclicTruncatedSectionsSystem_obj (m : ℕ) :
    (acyclicTruncatedSectionsSystem Φ F η T D hF hT).obj m =
      (Φ.mapHomologicalComplex _).obj ((T.truncatedResolutionSystem F η D).obj m) :=
  rfl

/-- Every level of `Φ(G^•)` is zero in degrees above `D + 1`. -/
lemma isZero_acyclicTruncatedSectionsSystem_obj_X (m : ℕ) {q : ℕ} (hq : D + 1 < q) :
    IsZero (((acyclicTruncatedSectionsSystem Φ F η T D hF hT).obj m).X q) :=
  Φ.map_isZero (T.isZero_truncatedResolutionSystem_obj_X F η D m hq)

include hF hT in
/-- The comparison map `Hⁿ(Φ(G_m^•)) ⟶ Rⁿ Φ(T m)` of the truncated resolution is an
isomorphism. -/
lemma isIso_truncatedResolutionComparison (m n : ℕ) :
    IsIso (AcyclicResolution.resolutionComparison Φ (T.truncatedResolutionAugmentation F η D m)
      n) :=
  (acyclicResolutionComparisonStatement C E Φ (T.obj m) _
    (T.truncatedResolutionAugmentation F η D m) inferInstance
    (fun i r => isZero_rightDerived_truncatedResolutionSystem_obj_X Φ F η T D hF hT m i r)
    (injectiveResolution _) _ (AcyclicResolution.comp_lift_id _ _)).2 n

/-- Harris (2.3): the cohomology of level `m` of the section complexes `Φ(G^•)` is the right
derived functor `Rⁿ Φ(T m)`, through the comparison map of the acyclic resolution `G_m^•`. -/
def acyclicTruncatedSectionsHomologyIso (m n : ℕ) :
    ((acyclicTruncatedSectionsSystem Φ F η T D hF hT).obj m).homology n ≅
      (Φ.rightDerived n).obj (T.obj m) :=
  @asIso _ _ _ _
    (AcyclicResolution.resolutionComparison Φ (T.truncatedResolutionAugmentation F η D m) n)
    (isIso_truncatedResolutionComparison Φ F η T D hF hT m n)

lemma acyclicTruncatedSectionsHomologyIso_hom (m n : ℕ) :
    (acyclicTruncatedSectionsHomologyIso Φ F η T D hF hT m n).hom =
      AcyclicResolution.resolutionComparison Φ (T.truncatedResolutionAugmentation F η D m) n :=
  rfl

/-- The cohomology of every level of `Φ(G^•)` vanishes in degrees above `D`. -/
lemma isZero_acyclicTruncatedSectionsSystem_homology (m : ℕ) {n : ℕ} (hn : D < n) :
    IsZero (((acyclicTruncatedSectionsSystem Φ F η T D hF hT).obj m).homology n) :=
  (hT m n hn).of_iso (acyclicTruncatedSectionsHomologyIso Φ F η T D hF hT m n)

end Acyclic

end DivisibleSystem

end Langlands.Cohomology
