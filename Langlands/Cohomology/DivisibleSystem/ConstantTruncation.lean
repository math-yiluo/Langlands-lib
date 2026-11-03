import Langlands.Cohomology.DivisibleSystem.ConstantCoefficients
import Langlands.Cohomology.DivisibleSystem.Invariants
import Langlands.Cohomology.DivisibleSystem.Sections

/-!
# Truncated constant Godement systems and their section complexes

Harris's truncated resolutions `G_m^• = τ_{≤D+1}(F_m^•)` of the constant sheaves `ℤ / ℓ ^ m ℤ`
(Lemma 2.2 bis) and their section complexes, obtained by specializing the published
truncation and section-complex systems to the published constant system `{R / ℓ ^ m R}`, with
explicit identifications of every level, differential and inclusion component.

* `truncation_obj_X_of_le`, `truncation_obj_X_top`, `truncation_obj_d_comp_eqToHom_of_lt`,
  `truncation_obj_d_comp_eqToHom_top`, `truncationHom_tower_app_f_of_le` and
  `truncationHom_tower_app_f_top` describe the levels of the generic `truncation` and of its
  inclusion `truncationHom`.
* For a system `T` of smooth sheaves, `smoothGodementTruncatedObjXIso` and
  `smoothGodementTruncatedObjXIsoTop` identify level `m` of
  `smoothGodementTruncatedResolutionSystem h T D` with the smooth Godement complex of `T m` in
  degrees `≤ D` and with the residual object `R^(D + 1)` of the cokernel construction in degree
  `D + 1`. Under them the differentials are those of the Godement complex and the cokernel
  projection `F^D ⟶ R^(D + 1)`, and the inclusion into `smoothGodementResolutionSystem h T` is
  the identity and the coaugmentation `R^(D + 1) ⟶ F^(D + 1)`.
  `smoothGodementTruncatedCoaugmentation` is Harris's `b : T ⟶ F^0` into degree zero.
* `smoothGodementTruncatedSectionsSystem h T D Φ hterm hres`, `smoothGodementSectionsSystem`
  and `smoothGodementTruncatedSectionsHom` are the published section systems for any additive
  sections functor `Φ` preserving finite limits. The published compact, invariant compact and
  `H`-quotient-invariant section systems are cases of the first one (`rfl`). Their level
  identifications are the images under `Φ` of the ones above.
* The declarations ending in `OfIso` transport these identifications along an isomorphism
  `e : T m ≅ F`.
* `constantGodementTruncatedResolutionSystem hℓ G X h D`, its inclusion, its coaugmentation and
  its section systems are the case `T = constantSheafSystem hℓ G X`. Their levels are identified
  with the smooth Godement complex of `constantLevelSheaf R ℓ G X m`, the locally constant sheaf
  of the trivial smooth representation `R / ℓ ^ m R`. The declarations starting with
  `intConstantGodement` are the case `R = ℤ`, with the locally constant sheaves of
  `ZMod (ℓ ^ m)`.

The exactness of the degree-zero smooth Godement functor
(`SmoothGodementZeroExactStatement R G X`) and the surjectivity of the sections functor on the
projections (`hterm`, `hres`, `hall`) are explicit hypotheses. No acyclicity is proved.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

namespace DivisibleSystem

section TruncationLevels

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
  (S : ℕ → DivisibleSystem C ℓ) (d : ∀ q, S q ⟶ S (q + 1))
  (sq : ∀ q m, (d q).tower.app m ≫ (d (q + 1)).tower.app m = 0)
  (D : ℕ) (Z : DivisibleSystem C ℓ) (p : S D ⟶ Z) (ι : Z ⟶ S (D + 1))
  [∀ m, Mono (ι.tower.app m)]
  (hpι : ∀ m, p.tower.app m ≫ ι.tower.app m = (d D).tower.app m)

/-- For `q ≤ D`, the degree-`q` term of level `m` of the truncation is `(S q) m`. -/
lemma truncation_obj_X_of_le (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((truncation S d sq D Z p ι hpι).obj m).X q = (S q).obj m :=
  congrArg (fun S : DivisibleSystem C ℓ => S.obj m) (truncationTerm_of_le S D Z hq)

/-- The degree-`(D + 1)` term of level `m` of the truncation is `Z m`. -/
lemma truncation_obj_X_top (m : ℕ) :
    ((truncation S d sq D Z p ι hpι).obj m).X (D + 1) = Z.obj m :=
  congrArg (fun S : DivisibleSystem C ℓ => S.obj m) (truncationTerm_of_eq S D Z rfl)

/-- For `q < D`, the differential of level `m` of the truncation in degree `q` is the
component of `d q`. -/
lemma truncation_obj_d_comp_eqToHom_of_lt (m : ℕ) {q : ℕ} (hq : q < D) :
    ((truncation S d sq D Z p ι hpι).obj m).d q (q + 1) ≫
        eqToHom (truncation_obj_X_of_le S d sq D Z p ι hpι m (Nat.succ_le_of_lt hq)) =
      eqToHom (truncation_obj_X_of_le S d sq D Z p ι hpι m hq.le) ≫ (d q).tower.app (op m) := by
  rw [comp_eqToHom_iff, truncation_obj_d, truncationDifferential_tower_app_of_lt S d D Z p hq,
    Category.assoc]
  rfl

/-- The differential of level `m` of the truncation in degree `D` is the component of `p`. -/
lemma truncation_obj_d_comp_eqToHom_top (m : ℕ) :
    ((truncation S d sq D Z p ι hpι).obj m).d D (D + 1) ≫
        eqToHom (truncation_obj_X_top S d sq D Z p ι hpι m) =
      eqToHom (truncation_obj_X_of_le S d sq D Z p ι hpι m le_rfl) ≫ p.tower.app (op m) := by
  rw [comp_eqToHom_iff, truncation_obj_d, truncationDifferential_tower_app_self S d D Z p,
    Category.assoc]
  rfl

/-- For `q ≤ D`, the components of the inverse of `truncationDegreeIsoOfLE` are the
identifications `truncation_obj_X_of_le`. -/
lemma truncationDegreeIsoOfLE_inv_tower_app (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    (truncationDegreeIsoOfLE S d sq D Z p ι hpι hq).inv.tower.app (op m) =
      eqToHom (truncation_obj_X_of_le S d sq D Z p ι hpι m hq).symm := by
  change (eqToHom (truncationTerm_of_le S D Z hq).symm).tower.app (op m) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact eqToHom_tower_app _ _

variable (hιd : ∀ m, ι.tower.app m ≫ (d (D + 1)).tower.app m = 0)

/-- In degrees `q ≤ D`, the inclusion of the truncation is the identity at every level. -/
lemma truncationHom_tower_app_f_of_le (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)).f q =
      eqToHom (truncation_obj_X_of_le S d sq D Z p ι hpι m hq) :=
  truncationInclusion_tower_app_of_le S D Z ι hq (op m)

/-- In degree `D + 1`, the inclusion of the truncation is the component of `ι` at every
level. -/
lemma truncationHom_tower_app_f_top (m : ℕ) :
    ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)).f (D + 1) =
      eqToHom (truncation_obj_X_top S d sq D Z p ι hpι m) ≫ ι.tower.app (op m) :=
  truncationInclusion_tower_app_top S D Z ι (op m)

end TruncationLevels

section SmoothGodementTruncation

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ)

/-- Every level of the truncated smooth Godement resolution system is zero in degrees above
`D + 1`. -/
lemma isZero_smoothGodementTruncatedResolutionSystem_obj_X (m : ℕ) {q : ℕ} (hq : D + 1 < q) :
    IsZero (((smoothGodementTruncatedResolutionSystem h T D).obj m).X q) := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact isZero_truncatedResolutionSystem_obj_X (smoothZeroFunctor R G X)
    (smoothCoaugmentation R G X) T D m hq

/-- Every level of the truncated smooth Godement resolution system is exact in positive
degrees. -/
lemma smoothGodementTruncatedResolutionSystem_obj_exactAt (m q : ℕ) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).ExactAt (q + 1) := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact truncatedResolutionSystem_obj_exactAt (smoothZeroFunctor R G X)
    (smoothCoaugmentation R G X) T D m q

/-- For `q ≤ D`, the degree-`q` term of level `m` of the truncated smooth Godement resolution
system is level `m` of the smooth Godement term system `F^q`. -/
lemma smoothGodementTruncatedResolutionSystem_obj_X_of_le (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).X q =
      (smoothGodementTermSystem h T q).obj m := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact congrArg (fun S : DivisibleSystem (SmoothTopologicalSheaf R G X) ℓ => S.obj m)
    (truncationTerm_of_le (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
      D (T.residualSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) (D + 1)) hq)

/-- The degree-`(D + 1)` term of level `m` of the truncated smooth Godement resolution system is
level `m` of the smooth Godement residual system `R (D + 1)`. -/
lemma smoothGodementTruncatedResolutionSystem_obj_X_top (m : ℕ) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).X (D + 1) =
      (smoothGodementResidualSystem h T (D + 1)).obj m := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact congrArg (fun S : DivisibleSystem (SmoothTopologicalSheaf R G X) ℓ => S.obj m)
    (truncationTerm_of_eq (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
      D (T.residualSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) (D + 1)) rfl)

/-- For `q ≤ D`, the degree-`q` term of level `m` of the truncated smooth Godement resolution
system is the degree-`q` term of the smooth Godement complex of `T m`. -/
def smoothGodementTruncatedObjXIso (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).X q ≅
      (smoothComplex R G X (T.obj m)).X q :=
  eqToIso (smoothGodementTruncatedResolutionSystem_obj_X_of_le h T D m hq) ≪≫
    smoothGodementTermSystemObjIso h T q m

/-- The levels of the smooth Godement residual systems are the residual objects of the
cokernel construction at the levels of `T`. -/
def smoothGodementResidualSystemObjIso (q m : ℕ) :
    (smoothGodementResidualSystem h T q).obj m ≅
      (CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) q).obj
        (T.obj m) :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  T.residualSystemObjIso (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) q (op m)

/-- The degree-`(D + 1)` term of level `m` of the truncated smooth Godement resolution system
is the residual object `R^(D + 1)` of the cokernel construction at `T m`. -/
def smoothGodementTruncatedObjXIsoTop (m : ℕ) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).X (D + 1) ≅
      (CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (D + 1)).obj (T.obj m) :=
  eqToIso (smoothGodementTruncatedResolutionSystem_obj_X_top h T D m) ≪≫
    smoothGodementResidualSystemObjIso h T (D + 1) m

/-- For `q < D`, the level isomorphisms carry the differentials of the truncated smooth
Godement resolution system to those of the smooth Godement complexes. -/
lemma smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIso_hom (m : ℕ) {q : ℕ}
    (hq : q < D) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).d q (q + 1) ≫
        (smoothGodementTruncatedObjXIso h T D m (Nat.succ_le_of_lt hq)).hom =
      (smoothGodementTruncatedObjXIso h T D m hq.le).hom ≫
        (smoothComplex R G X (T.obj m)).d q (q + 1) := by
  have := h.1
  have := h.2.1
  have := h.2.2
  simp only [smoothGodementTruncatedObjXIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  rw [← smoothGodementTermDifferential_comp_termSystemObjIso_hom]
  have h' := reassoc_of% (truncation_obj_d_comp_eqToHom_of_lt
    (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
    (T.termDifferential _ _) (T.termDifferential_comp_termDifferential_tower_app _ _) D
    (T.residualSystem _ _ (D + 1)) (T.residualQuotient _ _ D) (T.residualInclusion _ _ (D + 1))
    (fun m => (T.termDifferential_tower_app _ _ D m).symm) m hq)
  exact h' _

/-- In degree `D`, the level isomorphisms carry the differential of the truncated smooth
Godement resolution system to the cokernel projection `F^D ⟶ R^(D + 1)` at `T m`. -/
lemma smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTop_hom (m : ℕ) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).d D (D + 1) ≫
        (smoothGodementTruncatedObjXIsoTop h T D m).hom =
      (smoothGodementTruncatedObjXIso h T D m le_rfl).hom ≫
        (CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) D).app
          (T.obj m) := by
  have := h.1
  have := h.2.1
  have := h.2.2
  have key : (smoothGodementTermSystemObjIso h T D m).hom ≫
      (CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) D).app
        (T.obj m) =
      (T.residualQuotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) D).tower.app
          (op m) ≫ (smoothGodementResidualSystemObjIso h T (D + 1) m).hom :=
    (T.residualQuotient_comp_residualSystemObjIso_hom _ _ D (op m)).symm
  rw [smoothGodementTruncatedObjXIsoTop, smoothGodementTruncatedObjXIso, Iso.trans_hom,
    Iso.trans_hom, eqToIso.hom, eqToIso.hom]
  have h' := reassoc_of% (truncation_obj_d_comp_eqToHom_top
    (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
    (T.termDifferential _ _) (T.termDifferential_comp_termDifferential_tower_app _ _) D
    (T.residualSystem _ _ (D + 1)) (T.residualQuotient _ _ D) (T.residualInclusion _ _ (D + 1))
    (fun m => (T.termDifferential_tower_app _ _ D m).symm) m)
  exact (h' _).trans ((congrArg
    (eqToHom (smoothGodementTruncatedResolutionSystem_obj_X_of_le h T D m le_rfl) ≫ ·)
    key.symm).trans (Category.assoc _ _ _).symm)

/-- In degrees `q ≤ D`, the inclusion of the truncated smooth Godement resolution system is
the identity under the level isomorphisms. -/
lemma smoothGodementTruncatedResolutionHom_f_comp_objIso_hom_f (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedResolutionHom h T D).tower.app (op m)).f q ≫
        (smoothGodementResolutionSystemObjIso h T m).hom.f q =
      (smoothGodementTruncatedObjXIso h T D m hq).hom := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact congrArg (· ≫ (smoothGodementTermSystemObjIso h T q m).hom)
    (truncationHom_tower_app_f_of_le
      (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
      (T.termDifferential _ _) (T.termDifferential_comp_termDifferential_tower_app _ _) D
      (T.residualSystem _ _ (D + 1)) (T.residualQuotient _ _ D) (T.residualInclusion _ _ (D + 1))
      (fun m => (T.termDifferential_tower_app _ _ D m).symm)
      (T.residualInclusion_termDifferential_tower_app _ _ (D + 1)) m hq)

/-- In degree `D + 1`, the inclusion of the truncated smooth Godement resolution system is the
coaugmentation `R^(D + 1) ⟶ F^(D + 1)` at `T m` under the level isomorphisms. -/
lemma smoothGodementTruncatedResolutionHom_f_top_comp_objIso_hom_f (m : ℕ) :
    ((smoothGodementTruncatedResolutionHom h T D).tower.app (op m)).f (D + 1) ≫
        (smoothGodementResolutionSystemObjIso h T m).hom.f (D + 1) =
      (smoothGodementTruncatedObjXIsoTop h T D m).hom ≫
        (CokernelComplex.inclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).app (T.obj m) := by
  have := h.1
  have := h.2.1
  have := h.2.2
  have key : ((smoothGodementTruncatedResolutionHom h T D).tower.app (op m)).f (D + 1) =
      eqToHom (smoothGodementTruncatedResolutionSystem_obj_X_top h T D m) ≫
        (T.residualInclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).tower.app (op m) :=
    truncationHom_tower_app_f_top
      (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
      (T.termDifferential _ _) (T.termDifferential_comp_termDifferential_tower_app _ _) D
      (T.residualSystem _ _ (D + 1)) (T.residualQuotient _ _ D) (T.residualInclusion _ _ (D + 1))
      (fun m => (T.termDifferential_tower_app _ _ D m).symm)
      (T.residualInclusion_termDifferential_tower_app _ _ (D + 1)) m
  have key₂ : (T.residualInclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (D + 1)).tower.app (op m) ≫ (smoothGodementResolutionSystemObjIso h T m).hom.f (D + 1) =
      (T.residualSystemObjIso (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) (D + 1)
          (op m)).hom ≫
        (CokernelComplex.inclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).app (T.obj m) :=
    T.residualInclusion_comp_termSystemObjIso_hom _ _ (D + 1) (op m)
  rw [key]
  exact (Category.assoc _ _ _).trans
    ((congrArg (eqToHom (smoothGodementTruncatedResolutionSystem_obj_X_top h T D m) ≫ ·)
      key₂).trans (Category.assoc _ _ _).symm)

/-- For `q ≤ D`, the degree-`q` system of the truncated smooth Godement resolution system is
the smooth Godement term system `F^q`. -/
def smoothGodementTruncatedDegreeIsoOfLE {q : ℕ} (hq : q ≤ D) :
    (smoothGodementTruncatedResolutionSystem h T D).degree q ≅ smoothGodementTermSystem h T q :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncationDegreeIsoOfLE
    (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
    (T.termDifferential _ _) (T.termDifferential_comp_termDifferential_tower_app _ _) D
    (T.residualSystem _ _ (D + 1)) (T.residualQuotient _ _ D) (T.residualInclusion _ _ (D + 1))
    (fun m => (T.termDifferential_tower_app _ _ D m).symm) hq

/-- The components of the inverse of `smoothGodementTruncatedDegreeIsoOfLE` are the
identifications `smoothGodementTruncatedResolutionSystem_obj_X_of_le`. -/
lemma smoothGodementTruncatedDegreeIsoOfLE_inv_tower_app (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    (smoothGodementTruncatedDegreeIsoOfLE h T D hq).inv.tower.app (op m) =
      eqToHom (smoothGodementTruncatedResolutionSystem_obj_X_of_le h T D m hq).symm := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact truncationDegreeIsoOfLE_inv_tower_app
    (T.termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X))
    (T.termDifferential _ _) (T.termDifferential_comp_termDifferential_tower_app _ _) D
    (T.residualSystem _ _ (D + 1)) (T.residualQuotient _ _ D) (T.residualInclusion _ _ (D + 1))
    (fun m => (T.termDifferential_tower_app _ _ D m).symm) m hq

/-- Harris's morphism `b : T ⟶ F^0`, as a morphism into the degree-zero system of the
truncated smooth Godement resolution system. -/
def smoothGodementTruncatedCoaugmentation :
    T ⟶ (smoothGodementTruncatedResolutionSystem h T D).degree 0 :=
  smoothGodementCoaugmentation h T ≫ (smoothGodementTruncatedDegreeIsoOfLE h T D (Nat.zero_le D)).inv

/-- Under the level isomorphism in degree zero, the components of
`smoothGodementTruncatedCoaugmentation` are those of `b`. -/
lemma smoothGodementTruncatedCoaugmentation_tower_app_comp_objXIso_hom (m : ℕ) :
    (smoothGodementTruncatedCoaugmentation h T D).tower.app (op m) ≫
        (smoothGodementTruncatedObjXIso h T D m (Nat.zero_le D)).hom =
      (smoothGodementCoaugmentation h T).tower.app (op m) ≫
        (smoothGodementTermSystemObjIso h T 0 m).hom := by
  rw [smoothGodementTruncatedCoaugmentation, comp_tower, NatTrans.comp_app,
    smoothGodementTruncatedDegreeIsoOfLE_inv_tower_app, smoothGodementTruncatedObjXIso,
    Iso.trans_hom, eqToIso.hom]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((eqToHom_trans_assoc _ _ _).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _))))

end SmoothGodementTruncation

section SmoothGodementSections

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : SmoothTopologicalSheaf R G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]

/-- Harris's system of section complexes `{G_m(U)}` for a sections functor `Φ`: `Φ` applied
degreewise to the truncated smooth Godement resolution system, given that `Φ` maps the
projections of `F^q`, `q ≤ D`, and of `R (D + 1)` to epimorphisms. -/
def smoothGodementTruncatedSectionsSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex E ℕ) ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncatedResolutionSectionsSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T D
    Φ hterm hres

/-- `Φ` applied degreewise to the full smooth Godement resolution system, given that `Φ` maps
the projections of every `F^q` to epimorphisms. -/
def smoothGodementSectionsSystem
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm))) :
    DivisibleSystem (CochainComplex E ℕ) ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  resolutionSectionsSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T Φ hall

/-- `Φ` applied degreewise to the inclusion of the truncated smooth Godement resolution
system into the full one. -/
def smoothGodementTruncatedSectionsHom
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    smoothGodementTruncatedSectionsSystem h T D Φ (fun q _ => hall q) hres ⟶
      smoothGodementSectionsSystem h T Φ hall :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncatedResolutionSectionsHom (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T D
    Φ hall hres

/-- The published compact-section system is the case `Φ = Γ_c` of
`smoothGodementTruncatedSectionsSystem`. -/
lemma smoothGodementTruncatedCompactSectionsSystem_eq
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    smoothGodementTruncatedCompactSectionsSystem h T D hterm hres =
      smoothGodementTruncatedSectionsSystem h T D (smoothSheafCompactSections R G X) hterm hres :=
  rfl

/-- The published invariant compact-section system is the case `Φ = Γ_c(-)^G` of
`smoothGodementTruncatedSectionsSystem`. -/
lemma smoothGodementTruncatedInvariantCompactSectionsSystem_eq
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((SmoothSheafCohomology.invariantCompactSections R G X).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((SmoothSheafCohomology.invariantCompactSections R G X).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    smoothGodementTruncatedInvariantCompactSectionsSystem h T D hterm hres =
      smoothGodementTruncatedSectionsSystem h T D
        (SmoothSheafCohomology.invariantCompactSections R G X) hterm hres :=
  rfl

/-- The published system `{G_m(U)^H}` is the case `Φ = Γ_c(-)^H` of
`smoothGodementTruncatedSectionsSystem`. -/
lemma smoothGodementTruncatedQuotientInvariantSectionsSystem_eq (H : Subgroup G) [H.Normal]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    smoothGodementTruncatedQuotientInvariantSectionsSystem h T D H hterm hres =
      smoothGodementTruncatedSectionsSystem h T D
        (smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H) hterm hres :=
  rfl

variable (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- Every level of the truncated section complexes is zero in degrees above `D + 1`. -/
lemma isZero_smoothGodementTruncatedSectionsSystem_obj_X (m : ℕ) {q : ℕ} (hq : D + 1 < q) :
    IsZero (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).X q) :=
  Φ.map_isZero (isZero_smoothGodementTruncatedResolutionSystem_obj_X h T D m hq)

/-- For `q ≤ D`, the degree-`q` term of level `m` of the truncated section complexes is `Φ` of
the degree-`q` term of the smooth Godement complex of `T m`. -/
def smoothGodementTruncatedSectionsObjXIso (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).X q ≅
      Φ.obj ((smoothComplex R G X (T.obj m)).X q) :=
  Φ.mapIso (smoothGodementTruncatedObjXIso h T D m hq)

/-- The degree-`(D + 1)` term of level `m` of the truncated section complexes is `Φ` of the
residual object `R^(D + 1)` of the cokernel construction at `T m`. -/
def smoothGodementTruncatedSectionsObjXIsoTop (m : ℕ) :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).X (D + 1) ≅
      Φ.obj ((CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (D + 1)).obj (T.obj m)) :=
  Φ.mapIso (smoothGodementTruncatedObjXIsoTop h T D m)

/-- For `q < D`, the level isomorphisms carry the differentials of the truncated section
complexes to `Φ` of the differentials of the smooth Godement complexes. -/
lemma smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIso_hom (m : ℕ) {q : ℕ}
    (hq : q < D) :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).d q (q + 1) ≫
        (smoothGodementTruncatedSectionsObjXIso h T D Φ hterm hres m
          (Nat.succ_le_of_lt hq)).hom =
      (smoothGodementTruncatedSectionsObjXIso h T D Φ hterm hres m hq.le).hom ≫
        Φ.map ((smoothComplex R G X (T.obj m)).d q (q + 1)) :=
  (Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map (smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIso_hom h T D m hq)).trans
      (Φ.map_comp _ _))

/-- In degree `D`, the level isomorphisms carry the differential of the truncated section
complexes to `Φ` of the cokernel projection `F^D ⟶ R^(D + 1)` at `T m`. -/
lemma smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoTop_hom (m : ℕ) :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).d D (D + 1) ≫
        (smoothGodementTruncatedSectionsObjXIsoTop h T D Φ hterm hres m).hom =
      (smoothGodementTruncatedSectionsObjXIso h T D Φ hterm hres m le_rfl).hom ≫
        Φ.map ((CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          D).app (T.obj m)) :=
  (Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map (smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTop_hom h T D m)).trans
      (Φ.map_comp _ _))

/-- Level `m` of the full section complexes is `Φ` applied degreewise to the smooth Godement
complex of `T m`. -/
def smoothGodementSectionsObjIso
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm))) (m : ℕ) :
    (smoothGodementSectionsSystem h T Φ hall).obj m ≅
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (smoothComplex R G X (T.obj m)) :=
  (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (smoothGodementResolutionSystemObjIso h T m)

/-- In degrees `q ≤ D`, the inclusion of the truncated section complexes is the identity
under the level isomorphisms. -/
lemma smoothGodementTruncatedSectionsHom_f_comp_objIso_hom_f
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm))) (m : ℕ) {q : ℕ}
    (hq : q ≤ D) :
    ((smoothGodementTruncatedSectionsHom h T D Φ hall hres).tower.app (op m)).f q ≫
        (smoothGodementSectionsObjIso h T Φ hall m).hom.f q =
      (smoothGodementTruncatedSectionsObjXIso h T D Φ (fun q _ => hall q) hres m hq).hom :=
  (Φ.map_comp _ _).symm.trans
    (congrArg Φ.map (smoothGodementTruncatedResolutionHom_f_comp_objIso_hom_f h T D m hq))

/-- In degree `D + 1`, the inclusion of the truncated section complexes is `Φ` of the
coaugmentation `R^(D + 1) ⟶ F^(D + 1)` at `T m` under the level isomorphisms. -/
lemma smoothGodementTruncatedSectionsHom_f_top_comp_objIso_hom_f
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm))) (m : ℕ) :
    ((smoothGodementTruncatedSectionsHom h T D Φ hall hres).tower.app (op m)).f (D + 1) ≫
        (smoothGodementSectionsObjIso h T Φ hall m).hom.f (D + 1) =
      (smoothGodementTruncatedSectionsObjXIsoTop h T D Φ (fun q _ => hall q) hres m).hom ≫
        Φ.map ((CokernelComplex.inclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).app (T.obj m)) :=
  (Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map (smoothGodementTruncatedResolutionHom_f_top_comp_objIso_hom_f h T D m)).trans
      (Φ.map_comp _ _))

end SmoothGodementSections

section SmoothGodementLevelIso

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : SmoothTopologicalSheaf R G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
  (m : ℕ) {F : SmoothTopologicalSheaf R G X} (e : T.obj m ≅ F)

/-- For `q ≤ D` and an isomorphism `e : T m ≅ F`, the degree-`q` term of level `m` of the
truncated smooth Godement resolution system is the degree-`q` term of the smooth Godement
complex of `F`. -/
def smoothGodementTruncatedObjXIsoOfIso {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).X q ≅ (smoothComplex R G X F).X q :=
  smoothGodementTruncatedObjXIso h T D m hq ≪≫
    HomologicalComplex.Hom.isoApp ((smoothComplexFunctor R G X).mapIso e) q

/-- For an isomorphism `e : T m ≅ F`, the degree-`(D + 1)` term of level `m` of the truncated
smooth Godement resolution system is the residual object `R^(D + 1)` of the cokernel
construction at `F`. -/
def smoothGodementTruncatedObjXIsoTopOfIso :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).X (D + 1) ≅
      (CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (D + 1)).obj F :=
  smoothGodementTruncatedObjXIsoTop h T D m ≪≫
    (CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
      (D + 1)).mapIso e

/-- For an isomorphism `e : T m ≅ F`, level `m` of the smooth Godement resolution system is the
smooth Godement complex of `F`. -/
def smoothGodementResolutionSystemObjIsoOfIso :
    (smoothGodementResolutionSystem h T).obj m ≅ smoothComplex R G X F :=
  smoothGodementResolutionSystemObjIso h T m ≪≫ (smoothComplexFunctor R G X).mapIso e

/-- For `q < D`, the level isomorphisms along `e` carry the differentials of the truncated
smooth Godement resolution system to those of the smooth Godement complex of `F`. -/
lemma smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoOfIso_hom {q : ℕ}
    (hq : q < D) :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).d q (q + 1) ≫
        (smoothGodementTruncatedObjXIsoOfIso h T D m e (Nat.succ_le_of_lt hq)).hom =
      (smoothGodementTruncatedObjXIsoOfIso h T D m e hq.le).hom ≫
        (smoothComplex R G X F).d q (q + 1) := by
  simp only [smoothGodementTruncatedObjXIsoOfIso, Iso.trans_hom,
    HomologicalComplex.Hom.isoApp_hom]
  rw [reassoc_of% (smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIso_hom h T D m hq),
    Category.assoc, HomologicalComplex.Hom.comm]

/-- In degree `D`, the level isomorphisms along `e` carry the differential of the truncated
smooth Godement resolution system to the cokernel projection `F^D ⟶ R^(D + 1)` at `F`. -/
lemma smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTopOfIso_hom :
    ((smoothGodementTruncatedResolutionSystem h T D).obj m).d D (D + 1) ≫
        (smoothGodementTruncatedObjXIsoTopOfIso h T D m e).hom =
      (smoothGodementTruncatedObjXIsoOfIso h T D m e le_rfl).hom ≫
        (CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) D).app
          F := by
  simp only [smoothGodementTruncatedObjXIsoTopOfIso, smoothGodementTruncatedObjXIsoOfIso,
    Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.Hom.isoApp_hom]
  rw [reassoc_of% (smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTop_hom h T D m)]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) D).naturality
      e.hom).symm).trans (Category.assoc _ _ _).symm)

/-- In degrees `q ≤ D`, the inclusion of the truncated smooth Godement resolution system is the
identity under the level isomorphisms along `e`. -/
lemma smoothGodementTruncatedResolutionHom_f_comp_objIsoOfIso_hom_f {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedResolutionHom h T D).tower.app (op m)).f q ≫
        (smoothGodementResolutionSystemObjIsoOfIso h T m e).hom.f q =
      (smoothGodementTruncatedObjXIsoOfIso h T D m e hq).hom := by
  simp only [smoothGodementResolutionSystemObjIsoOfIso, smoothGodementTruncatedObjXIsoOfIso,
    Iso.trans_hom, HomologicalComplex.comp_f, HomologicalComplex.Hom.isoApp_hom]
  rw [reassoc_of% (smoothGodementTruncatedResolutionHom_f_comp_objIso_hom_f h T D m hq)]

/-- In degree `D + 1`, the inclusion of the truncated smooth Godement resolution system is the
coaugmentation `R^(D + 1) ⟶ F^(D + 1)` at `F` under the level isomorphisms along `e`. -/
lemma smoothGodementTruncatedResolutionHom_f_top_comp_objIsoOfIso_hom_f :
    ((smoothGodementTruncatedResolutionHom h T D).tower.app (op m)).f (D + 1) ≫
        (smoothGodementResolutionSystemObjIsoOfIso h T m e).hom.f (D + 1) =
      (smoothGodementTruncatedObjXIsoTopOfIso h T D m e).hom ≫
        (CokernelComplex.inclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).app F :=
  (congrArg (_ ≫ ·) (HomologicalComplex.comp_f _ _ _)).trans <|
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (smoothGodementTruncatedResolutionHom_f_top_comp_objIso_hom_f h T D m)).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg (_ ≫ ·) ((CokernelComplex.inclusion (smoothZeroFunctor R G X)
            (smoothCoaugmentation R G X) (D + 1)).naturality e.hom).symm).trans
            (Category.assoc _ _ _).symm

/-- For `q ≤ D` and an isomorphism `e : T m ≅ F`, the degree-`q` term of level `m` of the
truncated section complexes is `Φ` of the degree-`q` term of the smooth Godement complex
of `F`. -/
def smoothGodementTruncatedSectionsObjXIsoOfIso {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).X q ≅
      Φ.obj ((smoothComplex R G X F).X q) :=
  Φ.mapIso (smoothGodementTruncatedObjXIsoOfIso h T D m e hq)

/-- For an isomorphism `e : T m ≅ F`, the degree-`(D + 1)` term of level `m` of the truncated
section complexes is `Φ` of the residual object `R^(D + 1)` of the cokernel construction
at `F`. -/
def smoothGodementTruncatedSectionsObjXIsoTopOfIso :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).X (D + 1) ≅
      Φ.obj ((CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (D + 1)).obj F) :=
  Φ.mapIso (smoothGodementTruncatedObjXIsoTopOfIso h T D m e)

/-- For `q < D`, the level isomorphisms along `e` carry the differentials of the truncated
section complexes to `Φ` of the differentials of the smooth Godement complex of `F`. -/
lemma smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoOfIso_hom {q : ℕ} (hq : q < D) :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).d q (q + 1) ≫
        (smoothGodementTruncatedSectionsObjXIsoOfIso h T D Φ hterm hres m e
          (Nat.succ_le_of_lt hq)).hom =
      (smoothGodementTruncatedSectionsObjXIsoOfIso h T D Φ hterm hres m e hq.le).hom ≫
        Φ.map ((smoothComplex R G X F).d q (q + 1)) :=
  (Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map
      (smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoOfIso_hom h T D m e hq)).trans
      (Φ.map_comp _ _))

/-- In degree `D`, the level isomorphisms along `e` carry the differential of the truncated
section complexes to `Φ` of the cokernel projection `F^D ⟶ R^(D + 1)` at `F`. -/
lemma smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoTopOfIso_hom :
    ((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).d D (D + 1) ≫
        (smoothGodementTruncatedSectionsObjXIsoTopOfIso h T D Φ hterm hres m e).hom =
      (smoothGodementTruncatedSectionsObjXIsoOfIso h T D Φ hterm hres m e le_rfl).hom ≫
        Φ.map ((CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          D).app F) :=
  (Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map
      (smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTopOfIso_hom h T D m e)).trans
      (Φ.map_comp _ _))

/-- For an isomorphism `e : T m ≅ F`, level `m` of the full section complexes is `Φ` applied
degreewise to the smooth Godement complex of `F`. -/
def smoothGodementSectionsObjIsoOfIso
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm))) :
    (smoothGodementSectionsSystem h T Φ hall).obj m ≅
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (smoothComplex R G X F) :=
  (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (smoothGodementResolutionSystemObjIsoOfIso h T m e)

/-- In degrees `q ≤ D`, the inclusion of the truncated section complexes is the identity under
the level isomorphisms along `e`. -/
lemma smoothGodementTruncatedSectionsHom_f_comp_objIsoOfIso_hom_f
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm))) {q : ℕ} (hq : q ≤ D) :
    ((smoothGodementTruncatedSectionsHom h T D Φ hall hres).tower.app (op m)).f q ≫
        (smoothGodementSectionsObjIsoOfIso h T Φ m e hall).hom.f q =
      (smoothGodementTruncatedSectionsObjXIsoOfIso h T D Φ (fun q _ => hall q) hres m e
        hq).hom :=
  (Φ.map_comp _ _).symm.trans
    (congrArg Φ.map (smoothGodementTruncatedResolutionHom_f_comp_objIsoOfIso_hom_f h T D m e hq))

/-- In degree `D + 1`, the inclusion of the truncated section complexes is `Φ` of the
coaugmentation `R^(D + 1) ⟶ F^(D + 1)` at `F` under the level isomorphisms along `e`. -/
lemma smoothGodementTruncatedSectionsHom_f_top_comp_objIsoOfIso_hom_f
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm))) :
    ((smoothGodementTruncatedSectionsHom h T D Φ hall hres).tower.app (op m)).f (D + 1) ≫
        (smoothGodementSectionsObjIsoOfIso h T Φ m e hall).hom.f (D + 1) =
      (smoothGodementTruncatedSectionsObjXIsoTopOfIso h T D Φ (fun q _ => hall q) hres m
        e).hom ≫
        Φ.map ((CokernelComplex.inclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).app F) :=
  (Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map
      (smoothGodementTruncatedResolutionHom_f_top_comp_objIsoOfIso_hom_f h T D m e)).trans
      (Φ.map_comp _ _))

end SmoothGodementLevelIso

section ConstantGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] (h : SmoothGodementZeroExactStatement R G X) (D : ℕ)

variable (R ℓ) in
/-- Level `m` of the constant system: the locally constant sheaf of the trivial smooth
representation `R / ℓ ^ m R`. -/
abbrev constantLevelSheaf (m : ℕ) : SmoothTopologicalSheaf R G X :=
  (LocallyConstantSheaf.smoothFunctor R G X).obj
    ((smoothTrivialFunctor.{u, u, u} R G).obj (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))

/-- The level isomorphisms of `constantGodementResolutionSystem` are the level isomorphisms
along `constantSheafSystemObjIso`. -/
lemma constantGodementResolutionSystemObjIso_eq (m : ℕ) :
    constantGodementResolutionSystemObjIso hℓ G X h m =
      smoothGodementResolutionSystemObjIsoOfIso h (constantSheafSystem hℓ G X) m
        (constantSheafSystemObjIso hℓ G X m) :=
  rfl

/-- Harris's truncated system `{F^0 → ⋯ → F^D → R^(D + 1)}` for the constant system
`{R / ℓ ^ m R}`. -/
abbrev constantGodementTruncatedResolutionSystem :
    DivisibleSystem (CochainComplex (SmoothTopologicalSheaf R G X) ℕ) ℓ :=
  smoothGodementTruncatedResolutionSystem h (constantSheafSystem hℓ G X) D

/-- The inclusion of the truncated constant system into the full constant smooth Godement
resolution system. -/
abbrev constantGodementTruncatedResolutionHom :
    constantGodementTruncatedResolutionSystem hℓ G X h D ⟶
      constantGodementResolutionSystem hℓ G X h :=
  smoothGodementTruncatedResolutionHom h (constantSheafSystem hℓ G X) D

/-- Harris's morphism `b : T ⟶ F^0` for the constant system, into the degree-zero system of
the truncated constant system. -/
abbrev constantGodementTruncatedCoaugmentation :
    constantSheafSystem hℓ G X ⟶ (constantGodementTruncatedResolutionSystem hℓ G X h D).degree 0 :=
  smoothGodementTruncatedCoaugmentation h (constantSheafSystem hℓ G X) D

/-- For `q ≤ D`, the degree-`q` term of level `m` of the truncated constant system is the
degree-`q` term of the smooth Godement complex of the locally constant sheaf of
`R / ℓ ^ m R`. -/
def constantGodementTruncatedObjXIso (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((constantGodementTruncatedResolutionSystem hℓ G X h D).obj m).X q ≅
      (smoothComplex R G X (constantLevelSheaf R ℓ G X m)).X q :=
  smoothGodementTruncatedObjXIsoOfIso h _ D m (constantSheafSystemObjIso hℓ G X m) hq

/-- The degree-`(D + 1)` term of level `m` of the truncated constant system is the residual
object `R^(D + 1)` of the cokernel construction at the locally constant sheaf of
`R / ℓ ^ m R`. -/
def constantGodementTruncatedObjXIsoTop (m : ℕ) :
    ((constantGodementTruncatedResolutionSystem hℓ G X h D).obj m).X (D + 1) ≅
      (CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (D + 1)).obj (constantLevelSheaf R ℓ G X m) :=
  smoothGodementTruncatedObjXIsoTopOfIso h _ D m (constantSheafSystemObjIso hℓ G X m)

/-- For `q < D`, the level isomorphisms carry the differentials of the truncated constant
system to those of the smooth Godement complex of the locally constant sheaf of
`R / ℓ ^ m R`. -/
lemma constantGodementTruncatedResolutionSystem_obj_d_comp_objXIso_hom (m : ℕ) {q : ℕ}
    (hq : q < D) :
    ((constantGodementTruncatedResolutionSystem hℓ G X h D).obj m).d q (q + 1) ≫
        (constantGodementTruncatedObjXIso hℓ G X h D m (Nat.succ_le_of_lt hq)).hom =
      (constantGodementTruncatedObjXIso hℓ G X h D m hq.le).hom ≫
        (smoothComplex R G X (constantLevelSheaf R ℓ G X m)).d q (q + 1) :=
  smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoOfIso_hom h _ D m _ hq

/-- In degree `D`, the level isomorphisms carry the differential of the truncated constant
system to the cokernel projection `F^D ⟶ R^(D + 1)` at the locally constant sheaf of
`R / ℓ ^ m R`. -/
lemma constantGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTop_hom (m : ℕ) :
    ((constantGodementTruncatedResolutionSystem hℓ G X h D).obj m).d D (D + 1) ≫
        (constantGodementTruncatedObjXIsoTop hℓ G X h D m).hom =
      (constantGodementTruncatedObjXIso hℓ G X h D m le_rfl).hom ≫
        (CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) D).app
          (constantLevelSheaf R ℓ G X m) :=
  smoothGodementTruncatedResolutionSystem_obj_d_comp_objXIsoTopOfIso_hom h _ D m _

/-- In degrees `q ≤ D`, the inclusion of the truncated constant system is the identity under
the level isomorphisms. -/
lemma constantGodementTruncatedResolutionHom_f_comp_objIso_hom_f (m : ℕ) {q : ℕ}
    (hq : q ≤ D) :
    ((constantGodementTruncatedResolutionHom hℓ G X h D).tower.app (op m)).f q ≫
        (constantGodementResolutionSystemObjIso hℓ G X h m).hom.f q =
      (constantGodementTruncatedObjXIso hℓ G X h D m hq).hom :=
  smoothGodementTruncatedResolutionHom_f_comp_objIsoOfIso_hom_f h _ D m _ hq

/-- In degree `D + 1`, the inclusion of the truncated constant system is the coaugmentation
`R^(D + 1) ⟶ F^(D + 1)` at the locally constant sheaf of `R / ℓ ^ m R` under the level
isomorphisms. -/
lemma constantGodementTruncatedResolutionHom_f_top_comp_objIso_hom_f (m : ℕ) :
    ((constantGodementTruncatedResolutionHom hℓ G X h D).tower.app (op m)).f (D + 1) ≫
        (constantGodementResolutionSystemObjIso hℓ G X h m).hom.f (D + 1) =
      (constantGodementTruncatedObjXIsoTop hℓ G X h D m).hom ≫
        (CokernelComplex.inclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).app (constantLevelSheaf R ℓ G X m) :=
  smoothGodementTruncatedResolutionHom_f_top_comp_objIsoOfIso_hom_f h _ D m _

/-- Harris's system of compact-section complexes `{G_m(U)}` for the constant system. -/
abbrev constantGodementTruncatedCompactSectionsSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex (Langlands.SmoothRep.{u, u, u} R G) ℕ) ℓ :=
  smoothGodementTruncatedCompactSectionsSystem h (constantSheafSystem hℓ G X) D hterm hres

/-- The system of invariant compact-section complexes `{G_m(U)^G}` for the constant system. -/
abbrev constantGodementTruncatedInvariantCompactSectionsSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((SmoothSheafCohomology.invariantCompactSections R G X).map
        ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((SmoothSheafCohomology.invariantCompactSections R G X).map
        ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex (ModuleCat.{u} R) ℕ) ℓ :=
  smoothGodementTruncatedInvariantCompactSectionsSystem h (constantSheafSystem hℓ G X) D hterm
    hres

/-- Harris's system `{G_m(U)^H}` for the constant system and a normal subgroup `H`. -/
abbrev constantGodementTruncatedQuotientInvariantSectionsSystem (H : Subgroup G) [H.Normal]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℕ) ℓ :=
  smoothGodementTruncatedQuotientInvariantSectionsSystem h (constantSheafSystem hℓ G X) D H
    hterm hres

variable {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : SmoothTopologicalSheaf R G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map
        ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm)))

/-- The section complexes of the truncated constant system for a sections functor `Φ`. -/
abbrev constantGodementTruncatedSectionsSystem : DivisibleSystem (CochainComplex E ℕ) ℓ :=
  smoothGodementTruncatedSectionsSystem h (constantSheafSystem hℓ G X) D Φ hterm hres

/-- For `q ≤ D`, the degree-`q` term of level `m` of the constant section complexes is `Φ` of
the degree-`q` term of the smooth Godement complex of the locally constant sheaf of
`R / ℓ ^ m R`. -/
def constantGodementTruncatedSectionsObjXIso (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).obj m).X q ≅
      Φ.obj ((smoothComplex R G X (constantLevelSheaf R ℓ G X m)).X q) :=
  Φ.mapIso (constantGodementTruncatedObjXIso hℓ G X h D m hq)

/-- The degree-`(D + 1)` term of level `m` of the constant section complexes is `Φ` of the
residual object `R^(D + 1)` of the cokernel construction at the locally constant sheaf of
`R / ℓ ^ m R`. -/
def constantGodementTruncatedSectionsObjXIsoTop (m : ℕ) :
    ((constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).obj m).X (D + 1) ≅
      Φ.obj ((CokernelComplex.residual (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (D + 1)).obj (constantLevelSheaf R ℓ G X m)) :=
  Φ.mapIso (constantGodementTruncatedObjXIsoTop hℓ G X h D m)

/-- For `q < D`, the level isomorphisms carry the differentials of the constant section
complexes to `Φ` of the differentials of the smooth Godement complex of the locally constant
sheaf of `R / ℓ ^ m R`. -/
lemma constantGodementTruncatedSectionsSystem_obj_d_comp_objXIso_hom (m : ℕ) {q : ℕ}
    (hq : q < D) :
    ((constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).obj m).d q (q + 1) ≫
        (constantGodementTruncatedSectionsObjXIso hℓ G X h D Φ hterm hres m
          (Nat.succ_le_of_lt hq)).hom =
      (constantGodementTruncatedSectionsObjXIso hℓ G X h D Φ hterm hres m hq.le).hom ≫
        Φ.map ((smoothComplex R G X (constantLevelSheaf R ℓ G X m)).d q (q + 1)) :=
  smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoOfIso_hom h _ D Φ hterm hres m _ hq

/-- In degree `D`, the level isomorphisms carry the differential of the constant section
complexes to `Φ` of the cokernel projection `F^D ⟶ R^(D + 1)` at the locally constant sheaf of
`R / ℓ ^ m R`. -/
lemma constantGodementTruncatedSectionsSystem_obj_d_comp_objXIsoTop_hom (m : ℕ) :
    ((constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).obj m).d D (D + 1) ≫
        (constantGodementTruncatedSectionsObjXIsoTop hℓ G X h D Φ hterm hres m).hom =
      (constantGodementTruncatedSectionsObjXIso hℓ G X h D Φ hterm hres m le_rfl).hom ≫
        Φ.map ((CokernelComplex.quotient (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          D).app (constantLevelSheaf R ℓ G X m)) :=
  smoothGodementTruncatedSectionsSystem_obj_d_comp_objXIsoTopOfIso_hom h _ D Φ hterm hres m _

/-- The section complexes of the full constant smooth Godement resolution system. -/
abbrev constantGodementSectionsSystem
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm))) :
    DivisibleSystem (CochainComplex E ℕ) ℓ :=
  smoothGodementSectionsSystem h (constantSheafSystem hℓ G X) Φ hall

/-- Level `m` of the full constant section complexes is `Φ` applied degreewise to the smooth
Godement complex of the locally constant sheaf of `R / ℓ ^ m R`. -/
def constantGodementSectionsObjIso
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (m : ℕ) :
    (constantGodementSectionsSystem hℓ G X h Φ hall).obj m ≅
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (smoothComplex R G X (constantLevelSheaf R ℓ G X m)) :=
  (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (constantGodementResolutionSystemObjIso hℓ G X h m)

/-- `Φ` applied degreewise to the inclusion of the truncated constant system into the full
one. -/
abbrev constantGodementTruncatedSectionsHom
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm))) :
    constantGodementTruncatedSectionsSystem hℓ G X h D Φ (fun q _ => hall q) hres ⟶
      constantGodementSectionsSystem hℓ G X h Φ hall :=
  smoothGodementTruncatedSectionsHom h (constantSheafSystem hℓ G X) D Φ hall hres

/-- In degrees `q ≤ D`, the inclusion of the constant section complexes is the identity under
the level isomorphisms. -/
lemma constantGodementTruncatedSectionsHom_f_comp_objIso_hom_f
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((constantGodementTruncatedSectionsHom hℓ G X h D Φ hres hall).tower.app (op m)).f q ≫
        (constantGodementSectionsObjIso hℓ G X h Φ hall m).hom.f q =
      (constantGodementTruncatedSectionsObjXIso hℓ G X h D Φ (fun q _ => hall q) hres m
        hq).hom :=
  smoothGodementTruncatedSectionsHom_f_comp_objIsoOfIso_hom_f h _ D Φ hres m _ hall hq

/-- In degree `D + 1`, the inclusion of the constant section complexes is `Φ` of the
coaugmentation `R^(D + 1) ⟶ F^(D + 1)` at the locally constant sheaf of `R / ℓ ^ m R` under
the level isomorphisms. -/
lemma constantGodementTruncatedSectionsHom_f_top_comp_objIso_hom_f
    (hall : ∀ q, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (m : ℕ) :
    ((constantGodementTruncatedSectionsHom hℓ G X h D Φ hres hall).tower.app (op m)).f (D + 1) ≫
        (constantGodementSectionsObjIso hℓ G X h Φ hall m).hom.f (D + 1) =
      (constantGodementTruncatedSectionsObjXIsoTop hℓ G X h D Φ (fun q _ => hall q) hres
        m).hom ≫
        Φ.map ((CokernelComplex.inclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
          (D + 1)).app (constantLevelSheaf R ℓ G X m)) :=
  smoothGodementTruncatedSectionsHom_f_top_comp_objIsoOfIso_hom_f h _ D Φ hres m _ hall

end ConstantGodement

section IntConstantGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable (ℓ : ℕ) (hℓ : ℓ ≠ 0) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] (h : SmoothGodementZeroExactStatement ℤ G X) (D : ℕ)

/-- Harris's truncated system `{F^0 → ⋯ → F^D → R^(D + 1)}` for the constant system
`{ℤ / ℓ ^ m ℤ}`. -/
abbrev intConstantGodementTruncatedResolutionSystem :
    DivisibleSystem (CochainComplex (SmoothTopologicalSheaf ℤ G X) ℕ) ℓ :=
  smoothGodementTruncatedResolutionSystem h (intConstantSheafSystem ℓ hℓ G X) D

/-- For `q ≤ D`, the degree-`q` term of level `m` of the truncated system for `{ℤ / ℓ ^ m ℤ}` is
the degree-`q` term of the smooth Godement complex of the locally constant sheaf of
`ZMod (ℓ ^ m)`. -/
def intConstantGodementTruncatedObjXIso (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((intConstantGodementTruncatedResolutionSystem ℓ hℓ G X h D).obj m).X q ≅
      (smoothComplex ℤ G X ((LocallyConstantSheaf.smoothFunctor ℤ G X).obj
        ((smoothTrivialFunctor.{0, 0, 0} ℤ G).obj (ModuleCat.of ℤ (ZMod (ℓ ^ m)))))).X q :=
  smoothGodementTruncatedObjXIsoOfIso h _ D m (intConstantSheafSystemObjIso ℓ hℓ G X m) hq

/-- The degree-`(D + 1)` term of level `m` of the truncated system for `{ℤ / ℓ ^ m ℤ}` is the
residual object `R^(D + 1)` of the cokernel construction at the locally constant sheaf of
`ZMod (ℓ ^ m)`. -/
def intConstantGodementTruncatedObjXIsoTop (m : ℕ) :
    ((intConstantGodementTruncatedResolutionSystem ℓ hℓ G X h D).obj m).X (D + 1) ≅
      (CokernelComplex.residual (smoothZeroFunctor ℤ G X) (smoothCoaugmentation ℤ G X)
        (D + 1)).obj ((LocallyConstantSheaf.smoothFunctor ℤ G X).obj
          ((smoothTrivialFunctor.{0, 0, 0} ℤ G).obj (ModuleCat.of ℤ (ZMod (ℓ ^ m))))) :=
  smoothGodementTruncatedObjXIsoTopOfIso h _ D m (intConstantSheafSystemObjIso ℓ hℓ G X m)

variable {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : SmoothTopologicalSheaf ℤ G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (intConstantSheafSystem ℓ hℓ G X) q).projection
        hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h (intConstantSheafSystem ℓ hℓ G X)
        (D + 1)).projection hm)))

/-- The section complexes of the truncated system for `{ℤ / ℓ ^ m ℤ}` and a sections functor
`Φ`. -/
abbrev intConstantGodementTruncatedSectionsSystem : DivisibleSystem (CochainComplex E ℕ) ℓ :=
  smoothGodementTruncatedSectionsSystem h (intConstantSheafSystem ℓ hℓ G X) D Φ hterm hres

/-- For `q ≤ D`, the degree-`q` term of level `m` of the section complexes for
`{ℤ / ℓ ^ m ℤ}` is `Φ` of the degree-`q` term of the smooth Godement complex of the locally
constant sheaf of `ZMod (ℓ ^ m)`. -/
def intConstantGodementTruncatedSectionsObjXIso (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    ((intConstantGodementTruncatedSectionsSystem ℓ hℓ G X h D Φ hterm hres).obj m).X q ≅
      Φ.obj ((smoothComplex ℤ G X ((LocallyConstantSheaf.smoothFunctor ℤ G X).obj
        ((smoothTrivialFunctor.{0, 0, 0} ℤ G).obj (ModuleCat.of ℤ (ZMod (ℓ ^ m)))))).X q) :=
  Φ.mapIso (intConstantGodementTruncatedObjXIso ℓ hℓ G X h D m hq)

/-- The degree-`(D + 1)` term of level `m` of the section complexes for `{ℤ / ℓ ^ m ℤ}` is `Φ`
of the residual object `R^(D + 1)` of the cokernel construction at the locally constant sheaf
of `ZMod (ℓ ^ m)`. -/
def intConstantGodementTruncatedSectionsObjXIsoTop (m : ℕ) :
    ((intConstantGodementTruncatedSectionsSystem ℓ hℓ G X h D Φ hterm hres).obj m).X (D + 1) ≅
      Φ.obj ((CokernelComplex.residual (smoothZeroFunctor ℤ G X) (smoothCoaugmentation ℤ G X)
        (D + 1)).obj ((LocallyConstantSheaf.smoothFunctor ℤ G X).obj
          ((smoothTrivialFunctor.{0, 0, 0} ℤ G).obj (ModuleCat.of ℤ (ZMod (ℓ ^ m)))))) :=
  Φ.mapIso (intConstantGodementTruncatedObjXIsoTop ℓ hℓ G X h D m)

end IntConstantGodement

end DivisibleSystem

end Langlands.Cohomology
