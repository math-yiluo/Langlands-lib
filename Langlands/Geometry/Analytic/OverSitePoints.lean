import Langlands.Geometry.Analytic.EtaleGeometricPointEquivariance
import Langlands.Geometry.Analytic.QuasiEtaleSite

/-! # Fibre functors of field-valued points on sites of morphisms over an analytic space -/

noncomputable section

universe u v uL uG

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)))
  (L : Type uL) [NormedField L] [NormedAlgebra K L]

namespace OverSite

variable {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- The fibre functor of an `L`-valued point `x` of `X` on the category `P.Over ⊤ X` of
morphisms with property `P` to `X`: `U ⟶ X` goes to the set of `L`-valued points of `U` lying
over `x`. -/
def pointFibre (x : (localizedFieldPointFunctor L).obj X) : P.Over ⊤ X ⥤ Type (max u v uL) where
  obj U := {p : (localizedFieldPointFunctor L).obj U.left //
    (localizedFieldPointFunctor L).map U.hom p = x}
  map {U V} f := TypeCat.ofHom fun p => ⟨(localizedFieldPointFunctor L).map f.left p.1, by
    rw [← Functor.map_comp_apply, MorphismProperty.Over.w f]
    exact p.2⟩
  map_id U := by
    ext p
    exact (localizedFieldPointFunctor L).map_id_apply U.left p.1
  map_comp f g := by
    ext p
    exact (localizedFieldPointFunctor L).map_comp_apply f.left g.left p.1

/-- The point axioms for the fibre functor at `x` and a topology `J` on `P.Over ⊤ X`: the
category of elements is cofiltered, and every element over an object is the image of an
element over a member of each covering sieve. -/
def PointAxioms (J : GrothendieckTopology (P.Over ⊤ X)) (x : (localizedFieldPointFunctor L).obj X) :
    Prop :=
  IsCofiltered (pointFibre P L x).Elements ∧
    ∀ {U : P.Over ⊤ X} (R : Sieve U), R ∈ J U → ∀ p : (pointFibre P L x).obj U,
      ∃ (V : P.Over ⊤ X) (f : V ⟶ U) (_ : R f) (q : (pointFibre P L x).obj V),
        (pointFibre P L x).map f q = p

/-- The point of the site `(P.Over ⊤ X, J)` given by an `L`-valued point satisfying the point
axioms, with the fibre functor lifted to the universe of the site. -/
def toPoint (J : GrothendieckTopology (P.Over ⊤ X)) (x : (localizedFieldPointFunctor L).obj X)
    (h : PointAxioms P L J x) : J.Point.{max u (v + 1) uL} where
  fiber := pointFibre P L x ⋙ uliftFunctor.{max u (v + 1) uL, max u v uL}
  isCofiltered :=
    have := h.1
    IsCofiltered.of_equivalence (Functor.elementsULiftEquivalence _)
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR p := by
    obtain ⟨V, f, hf, q, hq⟩ := h.2 R hR p.down
    exact ⟨V, f, hf, ULift.up q, congrArg ULift.up hq⟩

@[simp]
theorem toPoint_fiber (J : GrothendieckTopology (P.Over ⊤ X))
    (x : (localizedFieldPointFunctor L).obj X) (h : PointAxioms P L J x) :
    (toPoint P L J x h).fiber = pointFibre P L x ⋙ uliftFunctor.{max u (v + 1) uL, max u v uL} :=
  rfl

variable [P.RespectsIso]

/-- Translation along `e : X ≅ Y`: `U ⟶ X` goes to the composite `U ⟶ X ⟶ Y`, with the same
morphisms. -/
def translate (e : X ≅ Y) : P.Over ⊤ X ≌ P.Over ⊤ Y :=
  MorphismProperty.Comma.mapRightIso (𝟭 _) (Discrete.natIso fun _ => e)

@[simp]
theorem translate_functor_obj_left (e : X ≅ Y) (U : P.Over ⊤ X) :
    ((translate P e).functor.obj U).left = U.left := rfl

@[simp]
theorem translate_functor_obj_hom (e : X ≅ Y) (U : P.Over ⊤ X) :
    ((translate P e).functor.obj U).hom = U.hom ≫ e.hom := rfl

@[simp]
theorem translate_functor_map_left (e : X ≅ Y) {U V : P.Over ⊤ X} (f : U ⟶ V) :
    ((translate P e).functor.map f).left = f.left := rfl

/-- Translation along `e : X ≅ Y` identifies the fibre over the image of `x` with the fibre
over `x`. -/
def pointFibreTranslate (e : X ≅ Y) (x : (localizedFieldPointFunctor L).obj X) :
    (translate P e).functor ⋙ pointFibre P L ((localizedFieldPointFunctor L).map e.hom x) ≅
      pointFibre P L x :=
  NatIso.ofComponents
    (fun U => (Equiv.subtypeEquivRight fun p => by
      change (localizedFieldPointFunctor L).map (U.hom ≫ e.hom) p = _ ↔ _
      rw [Functor.map_comp]
      exact ((localizedFieldPointFunctor L).mapIso e).toEquiv.injective.eq_iff).toIso)
    (fun _ => rfl)

/-- The lifted form of `pointFibreTranslate`, for the fibre functors of the points. -/
def pointTranslate {J : GrothendieckTopology (P.Over ⊤ X)} {J' : GrothendieckTopology (P.Over ⊤ Y)}
    (e : X ≅ Y) (x : (localizedFieldPointFunctor L).obj X) (hx : PointAxioms P L J x)
    (he : PointAxioms P L J' ((localizedFieldPointFunctor L).map e.hom x)) :
    (translate P e).functor ⋙ (toPoint P L J' _ he).fiber ≅ (toPoint P L J x hx).fiber :=
  Functor.isoWhiskerRight (pointFibreTranslate P L e x)
    uliftFunctor.{max u (v + 1) uL, max u v uL}

/-- For an action `ρ` of a group on `X` and points satisfying the point axioms for a topology
`J` on `P.Over ⊤ X`, the family of points indexed by the `L`-valued points, with the action
through `ρ`, is compatible with the translations `U ↦ gU`. -/
def pointEquivariance {G : Type uG} [Group G] (ρ : G →* Aut X)
    (J : GrothendieckTopology (P.Over ⊤ X))
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, PointAxioms P L J x) :
    letI := EtaleSite.pointAction L ρ
    Sheaf.Equivariant.TwistedOver.PointEquivariance (P := P) (J := J) ρ
      (fun x => toPoint P L J x (h x)) :=
  letI := EtaleSite.pointAction L ρ
  { fiberIso := fun g x => pointTranslate P L (ρ g) x (h x) (h _) }

end OverSite

/-! ## The étale site -/

theorem EtaleSite.pointFibre_eq {X : LocalizedCategory.{u, v, v} (K := K)}
    (x : (localizedFieldPointFunctor L).obj X) :
    EtaleSite.pointFibre L x = OverSite.pointFibre etale L x := rfl

theorem EtaleSite.pointAxioms_iff {X : LocalizedCategory.{u, v, v} (K := K)}
    (x : (localizedFieldPointFunctor L).obj X) :
    EtaleSite.PointAxioms L x ↔ OverSite.PointAxioms etale L (etaleTopology X) x := Iff.rfl

theorem EtaleSite.translate_eq {X Y : LocalizedCategory.{u, v, v} (K := K)} (e : X ≅ Y) :
    EtaleSite.translate e = OverSite.translate etale e := rfl

/-! ## The quasi-étale site -/

namespace QuasiEtaleSite

variable {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- Translation of the quasi-étale site along an isomorphism `e : X ≅ Y`. -/
abbrev translate (e : X ≅ Y) : QuasiEtaleSite X ≌ QuasiEtaleSite Y :=
  OverSite.translate quasiEtale e

/-- The fibre functor of an `L`-valued point `x` of `X` on the quasi-étale site. -/
abbrev pointFibre (x : (localizedFieldPointFunctor L).obj X) :
    QuasiEtaleSite X ⥤ Type (max u v uL) :=
  OverSite.pointFibre quasiEtale L x

/-- The point axioms for the fibre functor at `x` on the quasi-étale site. -/
abbrev PointAxioms (x : (localizedFieldPointFunctor L).obj X) : Prop :=
  OverSite.PointAxioms quasiEtale L (quasiEtaleTopology X) x

/-- The point of the quasi-étale site given by an `L`-valued point satisfying the point
axioms. -/
abbrev toPoint (x : (localizedFieldPointFunctor L).obj X) (h : PointAxioms L x) :
    (quasiEtaleTopology X).Point.{max u (v + 1) uL} :=
  OverSite.toPoint quasiEtale L (quasiEtaleTopology X) x h

/-- The lifted translation isomorphism of fibre functors on the quasi-étale site. -/
abbrev pointTranslate (e : X ≅ Y) (x : (localizedFieldPointFunctor L).obj X)
    (hx : PointAxioms L x) (he : PointAxioms L ((localizedFieldPointFunctor L).map e.hom x)) :
    (translate e).functor ⋙ (toPoint L _ he).fiber ≅ (toPoint L x hx).fiber :=
  OverSite.pointTranslate quasiEtale L e x hx he

/-- The family of points of the quasi-étale site indexed by the `L`-valued points is compatible
with the translations by a group acting on `X`. -/
abbrev pointEquivariance {G : Type uG} [Group G] (ρ : G →* Aut X)
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, PointAxioms L x) :
    letI := EtaleSite.pointAction L ρ
    Sheaf.Equivariant.TwistedOver.PointEquivariance (P := quasiEtale (K := K))
      (J := quasiEtaleTopology X) ρ (fun x => toPoint L x (h x)) :=
  OverSite.pointEquivariance quasiEtale L ρ (quasiEtaleTopology X) h

theorem translate_functor_eq {G : Type uG} [Group G] (ρ : G →* Aut X) (g : G) :
    (translate (ρ g)).functor = Sheaf.Equivariant.TwistedOver.translate quasiEtale ρ g := rfl

end QuasiEtaleSite

end Langlands.Analytic.SaturatedAtlasPresentation
