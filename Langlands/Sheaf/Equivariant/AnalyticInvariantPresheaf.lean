import Langlands.Sheaf.Equivariant.NaturalActionSections
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleGlobalComplex
import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedCompactComparison
import Langlands.Sheaf.Equivariant.AnalyticGSheaves
import Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite

/-!
# The presheaf of invariant sections `V(G) ↦ F(V)^G`

Let `X` be a `G`-space. An object `V(G)` of `Qét(X(G))` gives an object `V` of the twisted
quasi-étale site of `X` by forgetting the action, and the action of `g` on `V` is a twisted
endomorphism of `V` covering the action of `g` on `X`. The morphisms of `Qét(X(G))` commute
with these endomorphisms. So the sections over `V` of a sheaf `F` on the twisted site form a
representation of `G`, and `V(G) ↦ F(V)^G` is a presheaf of modules on `Qét(X(G))`. This is
the presheaf `(b_*F)^G` in the proof of Berkovich's Theorem 1.4.2. Its value at `X(G)` is
`Γ_{X(G)}(F)`. For a quasi-étale `G`-sheaf `F` and compact `V`, the representation of `G`
on `F(V)` is smooth. The same constructions are made for `Ét(X(G))`.

That the presheaf of invariant sections is a sheaf is not proved here.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z uR w

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type z} [Group G] [TopologicalSpace G] (X : GSpace.{u, v, v} K G)

section Lift

variable {X} in
/-- The action of `G` on a `G`-space `U` over `X` is a lift of the action on `X`, with open
subgroup `G`. -/
def gSpaceActionLift {U : GSpace.{u, v, v} K G} (f : U ⟶ X) :
    ActionLift X.obj.ρAut (GSpace.forget.map f) where
  subgroup := ⊤
  isOpen_subgroup := isOpen_univ
  action := U.obj.ρAut.comp (⊤ : Subgroup G).subtype
  isContinuousAction :=
    U.property.2.comp ⟨(⊤ : Subgroup G).subtype, continuous_subtype_val⟩
  equivariant h := f.hom.comm h

end Lift

section QuasiEtale

/-- An object `V(G)` of `Qét(X(G))` as an object of the twisted quasi-étale site of `X`: the
action on `V` is forgotten. -/
def quasiEtaleToTwisted :
    EquivariantQuasiEtaleSite X ⥤ TwistedOver (quasiEtale (K := K)) X.obj.ρAut :=
  EquivariantQuasiEtaleSite.toQuasiEtaleSite X ⋙ TwistedOver.ι _ _

/-- The twisted endomorphism of `V` given by the action of `g` on `V`: its twist is `g`. -/
def quasiEtaleGEndo (V : EquivariantQuasiEtaleSite X) (g : G) :
    (quasiEtaleToTwisted X).obj V ⟶ (quasiEtaleToTwisted X).obj V :=
  homMk g (V.left.obj.ρ g) (V.hom.hom.comm g)

@[simp]
theorem quasiEtaleGEndo_twist (V : EquivariantQuasiEtaleSite X) (g : G) :
    Hom.twist (quasiEtaleGEndo X V g) = g :=
  rfl

@[simp]
theorem quasiEtaleGEndo_left (V : EquivariantQuasiEtaleSite X) (g : G) :
    Hom.left (quasiEtaleGEndo X V g) = V.left.obj.ρ g :=
  rfl

theorem quasiEtaleGEndo_mul (V : EquivariantQuasiEtaleSite X) (g g' : G) :
    quasiEtaleGEndo X V (g * g') = quasiEtaleGEndo X V g' ≫ quasiEtaleGEndo X V g :=
  hom_ext rfl (by
    change V.left.obj.ρ (g * g') = V.left.obj.ρ g' ≫ V.left.obj.ρ g
    rw [map_mul]
    rfl)

theorem quasiEtaleGEndo_one (V : EquivariantQuasiEtaleSite X) :
    quasiEtaleGEndo X V 1 = 𝟙 _ :=
  hom_ext rfl (by
    change V.left.obj.ρ 1 = 𝟙 _
    rw [map_one]
    rfl)

/-- The natural action of `G` along `Qét(X(G)) → ` twisted quasi-étale site: `g` acts on `V`
by the endomorphism given by `g⁻¹`, so that `g` acts on sections by restriction along it. -/
def quasiEtaleNaturalAction : NaturalAction G (quasiEtaleToTwisted X) where
  act V :=
    { toFun := fun g => MulOpposite.op (quasiEtaleGEndo X V g⁻¹)
      map_one' := by
        rw [inv_one, quasiEtaleGEndo_one]
        rfl
      map_mul' := fun g g' => by
        apply MulOpposite.unop_injective
        rw [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op,
          MulOpposite.unop_op, mul_inv_rev, quasiEtaleGEndo_mul]
        rfl }
  comm {V W} f k := hom_ext
    (show (1 : G) * k⁻¹ = k⁻¹ * 1 by rw [one_mul, mul_one])
    (f.left.hom.comm k⁻¹)

@[simp]
theorem quasiEtaleNaturalAction_act_apply (V : EquivariantQuasiEtaleSite X) (g : G) :
    ((quasiEtaleNaturalAction X).act V g).unop = quasiEtaleGEndo X V g⁻¹ :=
  rfl

/-- The object `X(G)` of `Qét(X(G))`. -/
def equivariantQuasiEtaleBase : EquivariantQuasiEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) ((GSpace.quasiEtale (K := K) (G := G)).id_mem X)

/-- The object `X(G)` gives the base object of the twisted quasi-étale site. -/
theorem quasiEtaleToTwisted_obj_base :
    (quasiEtaleToTwisted X).obj (equivariantQuasiEtaleBase X) =
      base (quasiEtale (K := K)) X.obj.ρAut :=
  rfl

/-- At `X(G)`, the natural action is the action of `G` on the base object. -/
theorem quasiEtaleNaturalAction_act_base :
    (quasiEtaleNaturalAction X).act (equivariantQuasiEtaleBase X) =
      baseAction (quasiEtale (K := K)) X.obj.ρAut :=
  rfl

variable (R : Type uR) [CommRing R]

/-- The presheaf `V(G) ↦ F(V)^G` on `Qét(X(G))` of invariant sections of module sheaves on
the twisted quasi-étale site, functorially in the sheaf: Berkovich's `(b_*F)^G`. -/
def quasiEtaleInvariantPresheaf :
    Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤
      ((EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{w} R) :=
  (quasiEtaleNaturalAction X).sheafInvariantFunctor R (twistedQuasiEtaleTopology X.obj.ρAut)

/-- A section of `F` over `V` is invariant when it is fixed by restriction along the
action of every `g`. -/
theorem mem_quasiEtaleInvariantPresheaf_iff
    (F : Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R))
    (V : EquivariantQuasiEtaleSite X) (s : F.obj.obj (op ((quasiEtaleToTwisted X).obj V))) :
    s ∈ (actionRepresentation F.obj ((quasiEtaleNaturalAction X).act V)).invariants ↔
      ∀ g : G, (F.obj.map (quasiEtaleGEndo X V g⁻¹).op).hom s = s :=
  Iff.rfl

/-- The presheaf of invariant sections is left exact in the sheaf. -/
instance quasiEtaleInvariantPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (quasiEtaleInvariantPresheaf X R :
      Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤ _) :=
  inferInstanceAs (PreservesFiniteLimits
    ((quasiEtaleNaturalAction X).sheafInvariantFunctor R (twistedQuasiEtaleTopology X.obj.ρAut)))

/-- The value of the presheaf of invariant sections at `X(G)` is the module of invariant
global sections. -/
def quasiEtaleInvariantPresheafBaseIso :
    (quasiEtaleInvariantPresheaf X R :
      Sheaf (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{uR} R) ⥤ _) ⋙
        (CategoryTheory.evaluation (EquivariantQuasiEtaleSite X)ᵒᵖ (ModuleCat.{uR} R)).obj
          (op (equivariantQuasiEtaleBase X)) ≅
      sheafGlobalSectionsRep (quasiEtaleTopology X.obj.V) R
          (ρ := X.obj.ρAut) ⋙ Rep.invariantsFunctor R G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The presheaf `V(G) ↦ F(V)^G` on `Qét(X(G))` for quasi-étale `G`-sheaves. -/
def quasiEtaleGSheafInvariantPresheaf :
    QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤
      ((EquivariantQuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{w} R) :=
  (compactLiftSystem X.obj.ρAut).discreteSheafInclusion _ _ ⋙ quasiEtaleInvariantPresheaf X R

variable [HasSheafify (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R)]
variable [(compactLiftSystem X.obj.ρAut).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology X.obj.ρAut)]

/-- The presheaf of invariant sections is left exact on quasi-étale `G`-sheaves. -/
instance quasiEtaleGSheafInvariantPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (quasiEtaleGSheafInvariantPresheaf X R :
      QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ _) :=
  comp_preservesFiniteLimits _ _

end QuasiEtale

section QuasiEtaleBase

variable [IsTopologicalGroup G] (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The value at `X(G)` of the presheaf of invariant sections of a quasi-étale `G`-sheaf is
Berkovich's `Γ_{X(G)}(F)`. -/
def quasiEtaleGSheafInvariantPresheafBaseIso :
    quasiEtaleGSheafInvariantPresheaf X R ⋙
        (CategoryTheory.evaluation (EquivariantQuasiEtaleSite X)ᵒᵖ
          (ModuleCat.{max u (v + 1) uL} R)).obj (op (equivariantQuasiEtaleBase X)) ≅
      quasiEtaleGSheafInvariantSections.{u, v, uL} X.obj.ρAut R :=
  Functor.isoWhiskerLeft
      ((compactLiftSystem X.obj.ρAut).discreteSheafInclusion _ _)
      (quasiEtaleInvariantPresheafBaseIso X R) ≪≫
    Functor.isoWhiskerLeft
      ((compactLiftSystem X.obj.ρAut).discreteSheafInclusion _ _ ⋙
        sheafGlobalSectionsRep (quasiEtaleTopology X.obj.V) R
          (ρ := X.obj.ρAut))
      (smoothPartInvariantsIso R G).symm

end QuasiEtaleBase

section QuasiEtaleSmooth

variable (R : Type uR) [CommRing R]

/-- On a compact `V`, the action of `G` on `V` is admissible for the lifts on compact
quasi-étale objects. -/
theorem isAdmissible_quasiEtaleNaturalAction (V : EquivariantQuasiEtaleSite X)
    (hV : IsCompactSpace (GSpace.forget.obj V.left)) :
    (compactLiftSystem X.obj.ρAut).IsAdmissible ((quasiEtaleToTwisted X).obj V) ⊤
      (((quasiEtaleNaturalAction X).act V).comp ((⊤ : OpenSubgroup G) : Subgroup G).subtype) :=
  ⟨hV, gSpaceActionLift V.hom, fun _ _ => trivial, MonoidHom.ext fun _ => rfl⟩

/-- For a quasi-étale `G`-sheaf `F` and compact `V`, the representation of `G` on `F(V)` is
smooth. -/
theorem isSmooth_quasiEtaleGSheaf_sections
    (F : QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R)) (V : EquivariantQuasiEtaleSite X)
    (hV : IsCompactSpace (GSpace.forget.obj V.left)) :
    IsSmooth (actionRepresentation F.obj.obj ((quasiEtaleNaturalAction X).act V)) :=
  isSmooth_actionRepresentation_of_isAdmissible_top _
    (isAdmissible_quasiEtaleNaturalAction X V hV) F.property

/-- For compact `V`, the sections `F(V)` of quasi-étale `G`-sheaves, as smooth
representations of `G`. -/
def quasiEtaleGSheafSectionsSmooth (V : EquivariantQuasiEtaleSite X)
    (hV : IsCompactSpace (GSpace.forget.obj V.left)) :
    QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ SmoothRep.{uR, z, w} R G :=
  discreteSectionsSmoothOfTop R (compactLiftSystem X.obj.ρAut)
    (twistedQuasiEtaleTopology X.obj.ρAut) (isAdmissible_quasiEtaleNaturalAction X V hV)

instance quasiEtaleGSheafSectionsSmooth_additive (V : EquivariantQuasiEtaleSite X)
    (hV : IsCompactSpace (GSpace.forget.obj V.left)) :
    (quasiEtaleGSheafSectionsSmooth X R V hV :
      QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ SmoothRep.{uR, z, w} R G).Additive :=
  inferInstanceAs (discreteSectionsSmoothOfTop R (compactLiftSystem X.obj.ρAut)
    (twistedQuasiEtaleTopology X.obj.ρAut) (isAdmissible_quasiEtaleNaturalAction X V hV)).Additive

/-- For compact `V`, the value at `V(G)` of the presheaf of invariant sections is the module
of invariants of the smooth representation on `F(V)`. -/
def quasiEtaleGSheafInvariantPresheafEvaluationIso (V : EquivariantQuasiEtaleSite X)
    (hV : IsCompactSpace (GSpace.forget.obj V.left)) :
    (quasiEtaleGSheafInvariantPresheaf X R :
      QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ _) ⋙
        (CategoryTheory.evaluation (EquivariantQuasiEtaleSite X)ᵒᵖ (ModuleCat.{w} R)).obj (op V) ≅
      quasiEtaleGSheafSectionsSmooth X R V hV ⋙ smoothInvariantsFunctor R G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable [HasSheafify (twistedQuasiEtaleTopology X.obj.ρAut) (ModuleCat.{w} R)]
variable [(compactLiftSystem X.obj.ρAut).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology X.obj.ρAut)]

/-- For compact `V`, the smooth sections over `V` are left exact. -/
instance quasiEtaleGSheafSectionsSmooth_preservesFiniteLimits (V : EquivariantQuasiEtaleSite X)
    (hV : IsCompactSpace (GSpace.forget.obj V.left)) :
    PreservesFiniteLimits (quasiEtaleGSheafSectionsSmooth X R V hV :
      QuasiEtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ SmoothRep.{uR, z, w} R G) :=
  inferInstanceAs (PreservesFiniteLimits (discreteSectionsSmoothOfTop R
    (compactLiftSystem X.obj.ρAut) (twistedQuasiEtaleTopology X.obj.ρAut)
    (isAdmissible_quasiEtaleNaturalAction X V hV)))

end QuasiEtaleSmooth

section Etale

/-- An object `V(G)` of `Ét(X(G))` as an object of the twisted étale site of `X`: the action
on `V` is forgotten. -/
def etaleToTwisted : EquivariantEtaleSite X ⥤ TwistedOver (etale (K := K)) X.obj.ρAut :=
  EquivariantEtaleSite.toEtaleSite X ⋙ TwistedOver.ι _ _

/-- The twisted endomorphism of `V` given by the action of `g` on `V`: its twist is `g`. -/
def etaleGEndo (V : EquivariantEtaleSite X) (g : G) :
    (etaleToTwisted X).obj V ⟶ (etaleToTwisted X).obj V :=
  homMk g (V.left.obj.ρ g) (V.hom.hom.comm g)

@[simp]
theorem etaleGEndo_twist (V : EquivariantEtaleSite X) (g : G) :
    Hom.twist (etaleGEndo X V g) = g :=
  rfl

@[simp]
theorem etaleGEndo_left (V : EquivariantEtaleSite X) (g : G) :
    Hom.left (etaleGEndo X V g) = V.left.obj.ρ g :=
  rfl

theorem etaleGEndo_mul (V : EquivariantEtaleSite X) (g g' : G) :
    etaleGEndo X V (g * g') = etaleGEndo X V g' ≫ etaleGEndo X V g :=
  hom_ext rfl (by
    change V.left.obj.ρ (g * g') = V.left.obj.ρ g' ≫ V.left.obj.ρ g
    rw [map_mul]
    rfl)

theorem etaleGEndo_one (V : EquivariantEtaleSite X) : etaleGEndo X V 1 = 𝟙 _ :=
  hom_ext rfl (by
    change V.left.obj.ρ 1 = 𝟙 _
    rw [map_one]
    rfl)

/-- The natural action of `G` along `Ét(X(G)) → ` twisted étale site: `g` acts on `V` by the
endomorphism given by `g⁻¹`. -/
def etaleNaturalAction : NaturalAction G (etaleToTwisted X) where
  act V :=
    { toFun := fun g => MulOpposite.op (etaleGEndo X V g⁻¹)
      map_one' := by
        rw [inv_one, etaleGEndo_one]
        rfl
      map_mul' := fun g g' => by
        apply MulOpposite.unop_injective
        rw [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op,
          MulOpposite.unop_op, mul_inv_rev, etaleGEndo_mul]
        rfl }
  comm {V W} f k := hom_ext
    (show (1 : G) * k⁻¹ = k⁻¹ * 1 by rw [one_mul, mul_one])
    (f.left.hom.comm k⁻¹)

@[simp]
theorem etaleNaturalAction_act_apply (V : EquivariantEtaleSite X) (g : G) :
    ((etaleNaturalAction X).act V g).unop = etaleGEndo X V g⁻¹ :=
  rfl

/-- The object `X(G)` of `Ét(X(G))`. -/
def equivariantEtaleBase : EquivariantEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) ((GSpace.etale (K := K) (G := G)).id_mem X)

/-- The object `X(G)` gives the base object of the twisted étale site. -/
theorem etaleToTwisted_obj_base :
    (etaleToTwisted X).obj (equivariantEtaleBase X) = base (etale (K := K)) X.obj.ρAut :=
  rfl

/-- At `X(G)`, the natural action is the action of `G` on the base object. -/
theorem etaleNaturalAction_act_base :
    (etaleNaturalAction X).act (equivariantEtaleBase X) =
      baseAction (etale (K := K)) X.obj.ρAut :=
  rfl

variable (R : Type uR) [CommRing R]

/-- The presheaf `V(G) ↦ F(V)^G` on `Ét(X(G))` of invariant sections of module sheaves on
the twisted étale site, functorially in the sheaf. -/
def etaleInvariantPresheaf :
    Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤
      ((EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{w} R) :=
  (etaleNaturalAction X).sheafInvariantFunctor R (twistedEtaleTopology X.obj.ρAut)

/-- A section of `F` over `V` is invariant when it is fixed by restriction along the
action of every `g`. -/
theorem mem_etaleInvariantPresheaf_iff
    (F : Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{w} R))
    (V : EquivariantEtaleSite X) (s : F.obj.obj (op ((etaleToTwisted X).obj V))) :
    s ∈ (actionRepresentation F.obj ((etaleNaturalAction X).act V)).invariants ↔
      ∀ g : G, (F.obj.map (etaleGEndo X V g⁻¹).op).hom s = s :=
  Iff.rfl

/-- The presheaf of invariant sections is left exact in the sheaf. -/
instance etaleInvariantPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (etaleInvariantPresheaf X R :
      Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{w} R) ⥤ _) :=
  inferInstanceAs (PreservesFiniteLimits
    ((etaleNaturalAction X).sheafInvariantFunctor R (twistedEtaleTopology X.obj.ρAut)))

/-- The value of the presheaf of invariant sections at `X(G)` is the module of invariant
global sections. -/
def etaleInvariantPresheafBaseIso :
    (etaleInvariantPresheaf X R :
      Sheaf (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{uR} R) ⥤ _) ⋙
        (CategoryTheory.evaluation (EquivariantEtaleSite X)ᵒᵖ (ModuleCat.{uR} R)).obj
          (op (equivariantEtaleBase X)) ≅
      sheafGlobalSectionsRep (etaleTopology X.obj.V) R
          (ρ := X.obj.ρAut) ⋙ Rep.invariantsFunctor R G :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The presheaf `V(G) ↦ F(V)^G` on `Ét(X(G))` for étale `G`-sheaves. -/
def etaleGSheafInvariantPresheaf :
    EtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤
      ((EquivariantEtaleSite X)ᵒᵖ ⥤ ModuleCat.{w} R) :=
  (distinguishedLiftSystem X.obj.ρAut).smoothSheafInclusion _ _ ⋙ etaleInvariantPresheaf X R

variable [HasSheafify (twistedEtaleTopology X.obj.ρAut) (ModuleCat.{w} R)]
variable [(distinguishedLiftSystem X.obj.ρAut).HasAdmissibleRefinements
  (twistedEtaleTopology X.obj.ρAut)]

/-- The presheaf of invariant sections is left exact on étale `G`-sheaves. -/
instance etaleGSheafInvariantPresheaf_preservesFiniteLimits :
    PreservesFiniteLimits (etaleGSheafInvariantPresheaf X R :
      EtaleGSheaf X.obj.ρAut (ModuleCat.{w} R) ⥤ _) :=
  have : PreservesFiniteLimits ((distinguishedLiftSystem X.obj.ρAut).smoothSheafInclusion
      (ModuleCat.{w} R) (twistedEtaleTopology X.obj.ρAut)) := inferInstance
  comp_preservesFiniteLimits _ _

end Etale

section EtaleBase

variable [IsTopologicalGroup G] (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The value at `X(G)` of the presheaf of invariant sections of an étale `G`-sheaf is
Berkovich's `Γ_{X(G)}(F)`. -/
def etaleGSheafInvariantPresheafBaseIso :
    etaleGSheafInvariantPresheaf X R ⋙
        (CategoryTheory.evaluation (EquivariantEtaleSite X)ᵒᵖ
          (ModuleCat.{max u (v + 1) uL} R)).obj (op (equivariantEtaleBase X)) ≅
      etaleGSheafInvariantSections.{u, v, uL} X.obj.ρAut R :=
  Functor.isoWhiskerLeft
      ((distinguishedLiftSystem X.obj.ρAut).smoothSheafInclusion _ _)
      (etaleInvariantPresheafBaseIso X R) ≪≫
    Functor.isoWhiskerLeft
      ((distinguishedLiftSystem X.obj.ρAut).smoothSheafInclusion _ _ ⋙
        sheafGlobalSectionsRep (etaleTopology X.obj.V) R
          (ρ := X.obj.ρAut))
      (smoothPartInvariantsIso R G).symm

end EtaleBase

end Langlands.Sheaf.Equivariant.Analytic
