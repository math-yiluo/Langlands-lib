import Langlands.Cohomology.DivisibleSystem.LeftExact
import Langlands.Cohomology.DivisibleSystem.Truncation

/-!
# Sections of `ℓ`-divisible systems of complexes

Harris 1999, §2, p.305, passes from the truncated resolutions `G_m = τ_{≤ D+1}(F_m)` of
Lemma 2.2 bis to the complexes of sections `G_m(U(ẽ)_F̄)`, with cycles `Z_m^q = ker d_m^q`
and boundaries `B_m^q = im d_m^(q - 1)` in (2.3), and calls the resulting family "an
`ℓ`-divisible system of finite-length complexes [...], in the obvious sense".

This module applies an additive functor `Φ` preserving finite limits degreewise to an
`ℓ`-divisible system of cochain complexes, given that `Φ` maps every degree of every
projection `j` to an epimorphism; the result is again an `ℓ`-divisible system of cochain
complexes (`mapComplexes`). For the truncated resolution system the hypothesis is needed
only for the term systems `F^q`, `q ≤ D`, and for the residual system `R (D + 1)`, whose
projections Harris checks to be surjective on sections. The surjectivity is an explicit
hypothesis throughout; acyclicity and the cohomology of the section complexes are not
treated. The smooth specializations use compact sections and invariant compact sections of
smooth sheaves.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

namespace DivisibleSystem

section Complexes

variable {C : Type u} [Category.{v} C] [Abelian C] {E : Type u'} [Category.{v'} E] [Abelian E]
  {ℓ : ℕ} (K : DivisibleSystem (CochainComplex C ℕ) ℓ) (Φ : C ⥤ E) [Φ.Additive]
  [PreservesFiniteLimits Φ]
  (hΦ : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ.map ((K.projection h).f q)))

omit [PreservesFiniteLimits Φ] in
include hΦ in
/-- If `Φ` maps every degree of a projection to an epimorphism, `Φ` applied degreewise maps
the projection to an epimorphism of complexes. -/
lemma epi_mapHomologicalComplex_map_projection {m' m : ℕ} (h : m' ≤ m) :
    Epi ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map (K.projection h)) :=
  HomologicalComplex.epi_of_epi_f _ (fun q => hΦ h q)

/-- `Φ` applied degreewise to an `ℓ`-divisible system of cochain complexes, given that it maps
every degree of every projection to an epimorphism. -/
def mapComplexes : DivisibleSystem (CochainComplex E ℕ) ℓ :=
  K.mapLeftExact (Φ.mapHomologicalComplex (ComplexShape.up ℕ))
    (fun h => K.epi_mapHomologicalComplex_map_projection Φ hΦ h)

lemma mapComplexes_obj (m : ℕ) :
    (K.mapComplexes Φ hΦ).obj m = (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj (K.obj m) :=
  rfl

lemma mapComplexes_obj_X (m q : ℕ) : ((K.mapComplexes Φ hΦ).obj m).X q = Φ.obj ((K.obj m).X q) :=
  rfl

lemma mapComplexes_obj_d (m q q' : ℕ) :
    ((K.mapComplexes Φ hΦ).obj m).d q q' = Φ.map ((K.obj m).d q q') :=
  rfl

lemma mapComplexes_projection_f {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    ((K.mapComplexes Φ hΦ).projection h).f q = Φ.map ((K.projection h).f q) :=
  rfl

lemma mapComplexes_inclusion_f {m' m : ℕ} (h : m' < m) (q : ℕ) :
    ((K.mapComplexes Φ hΦ).inclusion h).f q = Φ.map ((K.inclusion h).f q) :=
  rfl

/-- The degree-`q` system of `mapComplexes` is the image under `Φ` of the degree-`q`
system. -/
lemma mapComplexes_degree (q : ℕ) :
    (K.mapComplexes Φ hΦ).degree q = (K.degree q).mapLeftExact Φ (fun h => hΦ h q) :=
  rfl

/-- `Φ` applied degreewise to a morphism of `ℓ`-divisible systems of cochain complexes. -/
def mapComplexesHom {K' : DivisibleSystem (CochainComplex C ℕ) ℓ} (f : K ⟶ K')
    (hΦ' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ.map ((K'.projection h).f q))) :
    K.mapComplexes Φ hΦ ⟶ K'.mapComplexes Φ hΦ' :=
  mapLeftExactHom _ _ (fun h => K.epi_mapHomologicalComplex_map_projection Φ hΦ h) f
    (fun h => K'.epi_mapHomologicalComplex_map_projection Φ hΦ' h)

lemma mapComplexesHom_tower_app_f {K' : DivisibleSystem (CochainComplex C ℕ) ℓ} (f : K ⟶ K')
    (hΦ' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ.map ((K'.projection h).f q)))
    (m : ℕᵒᵖ) (q : ℕ) :
    ((K.mapComplexesHom Φ hΦ f hΦ').tower.app m).f q = Φ.map ((f.tower.app m).f q) :=
  rfl

end Complexes

section Resolution

variable {C : Type u} [Category.{v} C] [Abelian C] {E : Type u'} [Category.{v'} E] [Abelian E]
  {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ) (D : ℕ)
  (Φ : C ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]

omit [PreservesFiniteLimits Φ] in
/-- If `Φ` maps the projections of the term systems `F^q`, `q ≤ D`, and of the residual
system `R (D + 1)` to epimorphisms, it maps every degree of every projection of the truncated
resolution system to an epimorphism. -/
lemma epi_map_truncatedResolutionSystem_projection_f
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (h : m' ≤ m), Epi (Φ.map ((T.termSystem F η q).projection h)))
    (hres : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi (Φ.map ((T.residualSystem F η (D + 1)).projection h)))
    {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    Epi (Φ.map (((T.truncatedResolutionSystem F η D).projection h).f q)) := by
  change Epi (Φ.map
    ((truncationTerm (T.termSystem F η) D (T.residualSystem F η (D + 1)) q).projection h))
  rcases lt_trichotomy q (D + 1) with hq | rfl | hq
  · rw [truncationTerm_of_le _ _ _ (by omega : q ≤ D)]
    exact hterm q (by omega) h
  · rw [truncationTerm_of_eq _ _ _ rfl]
    exact hres h
  · exact (Φ.map_isZero (isZero_truncationTerm_tower_obj _ _ _ hq (op m'))).epi _

/-- Harris's system of finite-length section complexes `{G_m(U)}`: `Φ` applied degreewise to
the truncated resolution system, given that `Φ` maps the projections of `F^q`, `q ≤ D`, and
of `R (D + 1)` to epimorphisms. -/
def truncatedResolutionSectionsSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (h : m' ≤ m), Epi (Φ.map ((T.termSystem F η q).projection h)))
    (hres : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi (Φ.map ((T.residualSystem F η (D + 1)).projection h))) :
    DivisibleSystem (CochainComplex E ℕ) ℓ :=
  (T.truncatedResolutionSystem F η D).mapComplexes Φ
    (fun h q => epi_map_truncatedResolutionSystem_projection_f F η T D Φ hterm hres h q)

/-- Every level of the truncated section complexes is zero in degrees above `D + 1`. -/
lemma isZero_truncatedResolutionSectionsSystem_obj_X
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (h : m' ≤ m), Epi (Φ.map ((T.termSystem F η q).projection h)))
    (hres : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi (Φ.map ((T.residualSystem F η (D + 1)).projection h)))
    (m : ℕ) {q : ℕ} (hq : D + 1 < q) :
    IsZero (((T.truncatedResolutionSectionsSystem F η D Φ hterm hres).obj m).X q) :=
  Φ.map_isZero (T.isZero_truncatedResolutionSystem_obj_X F η D m hq)

omit [Abelian E] [Φ.Additive] [PreservesFiniteLimits Φ] in
/-- If `Φ` maps the projections of every term system `F^q` to epimorphisms, it maps every
degree of every projection of the resolution system to an epimorphism. -/
lemma epi_map_resolutionSystem_projection_f
    (hall : ∀ q, ∀ {m' m : ℕ} (h : m' ≤ m), Epi (Φ.map ((T.termSystem F η q).projection h)))
    {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    Epi (Φ.map (((T.resolutionSystem F η).projection h).f q)) :=
  hall q h

/-- `Φ` applied degreewise to the resolution system, given that it maps the projections of
every term system to epimorphisms. -/
def resolutionSectionsSystem
    (hall : ∀ q, ∀ {m' m : ℕ} (h : m' ≤ m), Epi (Φ.map ((T.termSystem F η q).projection h))) :
    DivisibleSystem (CochainComplex E ℕ) ℓ :=
  (T.resolutionSystem F η).mapComplexes Φ
    (fun h q => epi_map_resolutionSystem_projection_f F η T Φ hall h q)

/-- `Φ` applied degreewise to the inclusion of the truncated resolution system. -/
def truncatedResolutionSectionsHom
    (hall : ∀ q, ∀ {m' m : ℕ} (h : m' ≤ m), Epi (Φ.map ((T.termSystem F η q).projection h)))
    (hres : ∀ {m' m : ℕ} (h : m' ≤ m),
      Epi (Φ.map ((T.residualSystem F η (D + 1)).projection h))) :
    T.truncatedResolutionSectionsSystem F η D Φ (fun q _ => hall q) hres ⟶
      T.resolutionSectionsSystem F η Φ hall :=
  mapComplexesHom _ Φ
    (fun h q =>
      epi_map_truncatedResolutionSystem_projection_f F η T D Φ (fun q _ => hall q) hres h q)
    (T.truncatedResolutionHom F η D)
    (fun h q => epi_map_resolutionSystem_projection_f F η T Φ hall h q)

end Resolution

section Smooth

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ)

/-- Compact sections of the truncated smooth Godement resolution system, as an `ℓ`-divisible
system of finite-length complexes of smooth representations, given that compact sections of
the projections of `F^q`, `q ≤ D`, and of `R (D + 1)` are epimorphisms. -/
def smoothGodementTruncatedCompactSectionsSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex (Langlands.SmoothRep.{u, u, u} R G) ℕ) ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncatedResolutionSectionsSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T D
    (smoothSheafCompactSections R G X) hterm hres

/-- Invariant compact sections of the truncated smooth Godement resolution system, as an
`ℓ`-divisible system of finite-length complexes of `R`-modules, given that invariant compact
sections of the projections of `F^q`, `q ≤ D`, and of `R (D + 1)` are epimorphisms. -/
def smoothGodementTruncatedInvariantCompactSectionsSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((SmoothSheafCohomology.invariantCompactSections R G X).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((SmoothSheafCohomology.invariantCompactSections R G X).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex (ModuleCat.{u} R) ℕ) ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncatedResolutionSectionsSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T D
    (SmoothSheafCohomology.invariantCompactSections R G X) hterm hres

end Smooth

end DivisibleSystem

end Langlands.Cohomology
