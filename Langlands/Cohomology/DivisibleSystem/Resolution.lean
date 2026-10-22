import Langlands.Cohomology.DivisibleSystem.Coaugmented

/-!
# `ℓ`-divisible systems of resolutions

A sequence of `ℓ`-divisible systems `S q` with morphisms `S q ⟶ S (q + 1)` whose
consecutive composites vanish at every level is an `ℓ`-divisible system of cochain
complexes: level `m` is the complex of the objects `S q m`, and all conditions hold
degreewise. Applied to the term systems of `Langlands.Cohomology.DivisibleSystem.Coaugmented`
this gives the `ℓ`-divisible system of the resolutions of Harris 1999, Lemma 2.2, whose
level `m` is the iterated-cokernel complex of `T m`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace DivisibleSystem

section OfDegrees

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
  (S : ℕ → DivisibleSystem C ℓ) (d : ∀ q, S q ⟶ S (q + 1))
  (sq : ∀ q m, (d q).tower.app m ≫ (d (q + 1)).tower.app m = 0)

/-- The cochain complex `S 0 m ⟶ S 1 m ⟶ ⋯` at level `m`. -/
abbrev levelComplex (m : ℕᵒᵖ) : CochainComplex C ℕ :=
  CochainComplex.of (fun q => (S q).tower.obj m) (fun q => (d q).tower.app m)
    (fun q => sq q m)

lemma levelComplex_d (m : ℕᵒᵖ) (q : ℕ) :
    (levelComplex S d sq m).d q (q + 1) = (d q).tower.app m :=
  CochainComplex.of_d (fun q => (S q).tower.obj m) (fun q => (d q).tower.app m) q

/-- The chain map between levels induced by the maps `j` of the systems `S q`. -/
def levelMap {m m' : ℕᵒᵖ} (f : m ⟶ m') : levelComplex S d sq m ⟶ levelComplex S d sq m' :=
  CochainComplex.ofHom (fun q => (S q).tower.map f) (fun q => by
    rw [levelComplex_d, levelComplex_d]
    exact (d q).tower.naturality f)

/-- The chain map between levels induced by the maps `i` of the systems `S q`. -/
def levelInclusion {m' m : ℕ} (h : m' < m) :
    levelComplex S d sq (op m') ⟶ levelComplex S d sq (op m) :=
  CochainComplex.ofHom (fun q => (S q).inclusion h) (fun q => by
    rw [levelComplex_d, levelComplex_d]
    exact (d q).comm h)

/-- The inverse system of the level complexes. -/
def complexTower : ℕᵒᵖ ⥤ CochainComplex C ℕ where
  obj m := levelComplex S d sq m
  map f := levelMap S d sq f
  map_id m := by
    ext q
    exact (S q).tower.map_id m
  map_comp f g := by
    ext q
    exact (S q).tower.map_comp f g

/-- The `ℓ`-divisible system of cochain complexes whose degree-`q` terms form the
system `S q`. All conditions hold degreewise. -/
def ofDegrees : DivisibleSystem (CochainComplex C ℕ) ℓ where
  tower := complexTower S d sq
  inclusion h := levelInclusion S d sq h
  powSMul_eq_zero m := by
    ext q
    exact (S q).powSMul_eq_zero m
  inclusion_comp h := by
    ext q
    exact (S q).inclusion_comp h
  shortExact h :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun q => (S q).shortExact h)
  torsion_exact h :=
    HomologicalComplex.exact_of_degreewise_exact _ (fun q => (S q).torsion_exact h)
  flat a b :=
    HomologicalComplex.exact_of_degreewise_exact _ (fun q => (S q).flat a b)

lemma ofDegrees_obj_X (m q : ℕ) : ((ofDegrees S d sq).obj m).X q = (S q).obj m :=
  rfl

lemma ofDegrees_obj_d (m q : ℕ) :
    ((ofDegrees S d sq).obj m).d q (q + 1) = (d q).tower.app (op m) :=
  levelComplex_d S d sq (op m) q

lemma ofDegrees_inclusion_f {m' m : ℕ} (h : m' < m) (q : ℕ) :
    ((ofDegrees S d sq).inclusion h).f q = (S q).inclusion h :=
  rfl

lemma ofDegrees_projection_f {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    ((ofDegrees S d sq).projection h).f q = (S q).projection h :=
  rfl

/-- The degree-`q` system of `ofDegrees S d sq` is `S q`. -/
def ofDegreesDegreeIso (q : ℕ) : (ofDegrees S d sq).degree q ≅ S q where
  hom :=
    { tower :=
        { app := fun m => 𝟙 ((S q).tower.obj m)
          naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm }
      comm := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm }
  inv :=
    { tower :=
        { app := fun m => 𝟙 ((S q).tower.obj m)
          naturality := fun _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm }
      comm := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm }
  hom_inv_id := by
    ext m
    exact Category.comp_id _
  inv_hom_id := by
    ext m
    exact Category.comp_id _

end OfDegrees

section Coaugmented

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ)

/-- The `ℓ`-divisible system of the resolutions `F^0 ⟶ F^1 ⟶ ⋯` of Harris's Lemma 2.2. -/
def resolutionSystem : DivisibleSystem (CochainComplex C ℕ) ℓ :=
  ofDegrees (T.termSystem F η) (T.termDifferential F η)
    (T.termDifferential_comp_termDifferential_tower_app F η)

/-- The degree-`q` system of the resolutions is the term system `F^q`. -/
def resolutionSystemDegreeIso (q : ℕ) :
    (T.resolutionSystem F η).degree q ≅ T.termSystem F η q :=
  ofDegreesDegreeIso _ _ _ q

lemma resolutionSystem_obj_d (m q : ℕ) :
    ((T.resolutionSystem F η).obj m).d q (q + 1) = (T.termDifferential F η q).tower.app (op m) :=
  ofDegrees_obj_d _ _ _ m q

/-- Level `m` of the resolution system is the iterated-cokernel complex of `T m`. -/
def resolutionSystemObjIso (m : ℕ) :
    (T.resolutionSystem F η).obj m ≅ CokernelComplex.complex F η (T.obj m) :=
  HomologicalComplex.Hom.isoOfComponents (fun q => T.termSystemObjIso F η q (op m)) (by
    intro q j (hj : q + 1 = j)
    subst hj
    rw [CokernelComplex.complex_d]
    exact (T.termDifferential_comp_termSystemObjIso_hom F η q (op m)).symm.trans
      (congrArg (· ≫ (T.termSystemObjIso F η (q + 1) (op m)).hom)
        (T.resolutionSystem_obj_d F η m q).symm))

/-- Every level of the resolution system is exact in positive degrees. -/
lemma resolutionSystem_obj_exactAt (m q : ℕ) :
    ((T.resolutionSystem F η).obj m).ExactAt (q + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (CochainComplex.prev_nat_succ q)
    (CochainComplex.next ℕ (q + 1))]
  exact shortComplex_exact_congr (T.resolutionSystem_obj_d F η m q).symm
    (T.resolutionSystem_obj_d F η m (q + 1)).symm (T.termDifferential_exact F η q m)

end Coaugmented

section Smooth

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)

/-- The `ℓ`-divisible system of the smooth Godement complexes of the levels of `T`, given
that the degree-zero smooth Godement functor is exact. -/
def smoothGodementResolutionSystem :
    DivisibleSystem (CochainComplex (SmoothTopologicalSheaf R G X) ℕ) ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  resolutionSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T

/-- Level `m` of the smooth Godement resolution system is the smooth Godement complex
of `T m`. -/
def smoothGodementResolutionSystemObjIso (m : ℕ) :
    (smoothGodementResolutionSystem h T).obj m ≅ smoothComplex R G X (T.obj m) :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  resolutionSystemObjIso (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T m

end Smooth

end DivisibleSystem

end Langlands.Cohomology
