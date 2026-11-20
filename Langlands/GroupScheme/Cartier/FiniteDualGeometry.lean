import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.Cartier.Characters
import Langlands.GroupScheme.Cartier.RelativeHomSheaf
import Langlands.AlgebraicGeometry.Picard.FiniteWeilPrincipalCartierPerfectness
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-! # Geometric input for finite locally free Cartier duality -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Cartier.FiniteDual

section Spectrum

variable {R : CommRingCat.{u}} (B : Type u) [CommRing B] [Algebra R B]

/-- The relative spectrum of an `R`-algebra is finite over `Spec R` exactly when the algebra is
a finite `R`-module. -/
theorem isFinite_algSpec_iff :
    IsFinite ((algSpec R).obj (op (CommAlgCat.of R B))).hom ↔ Module.Finite R B := by
  rw [algSpec_obj_hom, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap

/-- The relative spectrum of an `R`-algebra is flat over `Spec R` exactly when the algebra is a
flat `R`-module. -/
theorem flat_algSpec_iff :
    Flat ((algSpec R).obj (op (CommAlgCat.of R B))).hom ↔ Module.Flat R B := by
  rw [algSpec_obj_hom, Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff

/-- The relative spectrum of an `R`-algebra is locally of finite presentation over `Spec R`
exactly when the algebra is finitely presented. -/
theorem locallyOfFinitePresentation_algSpec_iff :
    LocallyOfFinitePresentation ((algSpec R).obj (op (CommAlgCat.of R B))).hom ↔
      Algebra.FinitePresentation R B := by
  rw [algSpec_obj_hom, LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap

/-- The relative spectrum of a finite projective `R`-algebra is finite, flat and locally of
finite presentation over `Spec R`. -/
theorem algSpec_finiteLocallyFree [Module.Finite R B] [Module.Projective R B] :
    IsFinite ((algSpec R).obj (op (CommAlgCat.of R B))).hom ∧
      Flat ((algSpec R).obj (op (CommAlgCat.of R B))).hom ∧
        LocallyOfFinitePresentation ((algSpec R).obj (op (CommAlgCat.of R B))).hom := by
  have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  exact ⟨(isFinite_algSpec_iff B).2 inferInstance, (flat_algSpec_iff B).2 inferInstance,
    (locallyOfFinitePresentation_algSpec_iff B).2 inferInstance⟩

end Spectrum

section Coordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))

/-- A group scheme that is finite over an affine base has affine total space. -/
theorem isAffine_of_isFinite [IsFinite G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

variable [IsAffine G.X.left]

/-- The structure map of the spectrum of the coordinate Hopf algebra factors through the
comparison isomorphism with the group scheme. -/
theorem hopfSpec_hom_eq :
    ((hopfSpec R).obj (op (AffineCoordinates.hopfAlgebra G))).X.hom =
      (AffineCoordinates.hopfSpecIso G).hom.hom.hom.left ≫ G.X.hom :=
  (Over.w (AffineCoordinates.hopfSpecIso G).hom.hom.hom).symm

/-- The coordinate Hopf algebra of a finite group scheme is a finite module. -/
theorem hopfAlgebra_finite [IsFinite G.X.hom] :
    Module.Finite R (AffineCoordinates.hopfAlgebra G) := by
  rw [← isFinite_algSpec_iff]
  change IsFinite ((hopfSpec R).obj (op (AffineCoordinates.hopfAlgebra G))).X.hom
  rw [hopfSpec_hom_eq]
  infer_instance

/-- The coordinate Hopf algebra of a flat group scheme is a flat module. -/
theorem hopfAlgebra_flat [Flat G.X.hom] :
    Module.Flat R (AffineCoordinates.hopfAlgebra G) := by
  rw [← flat_algSpec_iff]
  change Flat ((hopfSpec R).obj (op (AffineCoordinates.hopfAlgebra G))).X.hom
  rw [hopfSpec_hom_eq]
  infer_instance

/-- The coordinate Hopf algebra of a group scheme locally of finite presentation is finitely
presented. -/
theorem hopfAlgebra_finitePresentation [LocallyOfFinitePresentation G.X.hom] :
    Algebra.FinitePresentation R (AffineCoordinates.hopfAlgebra G) := by
  rw [← locallyOfFinitePresentation_algSpec_iff]
  change LocallyOfFinitePresentation
    ((hopfSpec R).obj (op (AffineCoordinates.hopfAlgebra G))).X.hom
  rw [hopfSpec_hom_eq]
  infer_instance

/-- The coordinate Hopf algebra of a finite, flat group scheme locally of finite presentation
is a projective module. -/
theorem hopfAlgebra_projective [IsFinite G.X.hom] [Flat G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] :
    Module.Projective R (AffineCoordinates.hopfAlgebra G) := by
  have := hopfAlgebra_finite G
  have := hopfAlgebra_flat G
  have := hopfAlgebra_finitePresentation G
  have : Module.FinitePresentation R (AffineCoordinates.hopfAlgebra G) :=
    Module.FinitePresentation.of_finite_of_finitePresentation R _
  exact Module.Flat.projective_of_finitePresentation

end Coordinates

section Transport

variable {S : Scheme.{u}}

/-- Precomposition along an isomorphism identifies the character functors. -/
def charactersIso {G G' : CommGroupScheme S} (e : G ≅ G') : characters G' ≅ characters G where
  hom := charactersMap e.hom
  inv := charactersMap e.inv
  hom_inv_id := by rw [← charactersMap_comp, e.inv_hom_id, charactersMap_id]
  inv_hom_id := by rw [← charactersMap_comp, e.hom_inv_id, charactersMap_id]

/-- The conclusion of finite locally free Cartier duality transfers along an isomorphism of
commutative group schemes. -/
theorem finiteCartierDual_of_iso {R : CommRingCat.{u}} {G G' : CommGroupScheme (Spec R)}
    (e : G ≅ G')
    (h : ∃ (D : CommGroupScheme (Spec R))
        (dual : additivePoints D.toGrp ≅ characters G')
        (bidual : additivePoints G'.toGrp ≅ characters D),
        IsFinite D.X.hom ∧ Flat D.X.hom ∧ LocallyOfFinitePresentation D.X.hom ∧
          ∀ (T : Over (Spec R)) (x : T ⟶ G'.X) (y : T ⟶ D.X),
            evaluation (bidual.hom.app (op T) (Additive.ofMul x)) y =
              evaluation (dual.hom.app (op T) (Additive.ofMul y)) x) :
    ∃ (D : CommGroupScheme (Spec R))
        (dual : additivePoints D.toGrp ≅ characters G)
        (bidual : additivePoints G.toGrp ≅ characters D),
        IsFinite D.X.hom ∧ Flat D.X.hom ∧ LocallyOfFinitePresentation D.X.hom ∧
          ∀ (T : Over (Spec R)) (x : T ⟶ G.X) (y : T ⟶ D.X),
            evaluation (bidual.hom.app (op T) (Additive.ofMul x)) y =
              evaluation (dual.hom.app (op T) (Additive.ofMul y)) x := by
  obtain ⟨D, dual, bidual, hfin, hflat, hlfp, heval⟩ := h
  refine ⟨D, dual ≪≫ charactersIso e, additivePointsIso e ≪≫ bidual, hfin, hflat, hlfp, ?_⟩
  intro T x y
  change evaluation (bidual.hom.app (op T) (Additive.ofMul (x ≫ e.hom.toMul.hom.hom))) y =
    characterEvaluation ((charactersMap e.hom).app (op T) (dual.hom.app (op T) (Additive.ofMul y))) x
  rw [characterEvaluation_precompose, heval]
  rfl

end Transport

section Local

variable {S : Scheme.{u}}

/-- A sieve containing every arrow from a relative scheme with affine source is a Zariski
covering sieve. -/
theorem affineTests_mem_zariski {T : Over S} (s : Sieve T)
    (hs : ∀ (V : Over S) (f : V ⟶ T), IsAffine V.left → s f) :
    s ∈ (Scheme.zariskiTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff]
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology T.left.affineCover)
  rintro Z g ⟨W, h, k, ⟨i⟩, rfl⟩
  apply Sieve.downward_closed
  rw [Sieve.overEquiv_iff]
  exact hs _ _ (Scheme.isAffine_affineCover T.left i)

/-- A morphism of Zariski sheaves of abelian groups on relative schemes is an isomorphism once
it is bijective on every test with affine source. -/
theorem isIso_of_bijective_affine {F G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G) (α : F ⟶ G)
    (h : ∀ T : Over S, IsAffine T.left → Function.Bijective (α.app (op T))) : IsIso α := by
  have hinj : Presheaf.IsLocallyInjective (Scheme.zariskiTopology.over S) α := ⟨fun {X} x y hxy => by
    apply affineTests_mem_zariski
    intro V f hV
    apply (h V hV).1
    change (F.map f.op ≫ α.app (op V)) x = (F.map f.op ≫ α.app (op V)) y
    rw [α.naturality]
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hxy]⟩
  have hsurj : Presheaf.IsLocallySurjective (Scheme.zariskiTopology.over S) α := ⟨fun {U} s => by
    apply affineTests_mem_zariski
    intro V f hV
    exact (h V hV).2 _⟩
  let α' : (⟨F, hF⟩ : Sheaf (Scheme.zariskiTopology.over S) AddCommGrpCat.{u}) ⟶ ⟨G, hG⟩ :=
    ObjectProperty.homMk α
  have : IsIso α' := (Sheaf.isLocallyBijective_iff_isIso α').1 ⟨hinj, hsurj⟩
  exact (inferInstance : IsIso ((sheafToPresheaf _ _).map α'))

/-- Bijectivity of a component of a natural transformation of abelian-group-valued presheaves
transfers along isomorphisms of test objects. -/
theorem bijective_app_of_iso {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : F ⟶ G) {T T' : C} (e : T ≅ T') (h : Function.Bijective (α.app (op T'))) :
    Function.Bijective (α.app (op T)) := by
  rw [← ConcreteCategory.isIso_iff_bijective] at h ⊢
  have : IsIso (F.map e.hom.op ≫ α.app (op T)) := by
    rw [α.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map e.hom.op) (α.app (op T))

/-- The point functor of a commutative group scheme, written additively, is a sheaf for every
subcanonical topology. -/
theorem isSheaf_additivePoints (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (G : Grp (Over S)) [IsCommMonObj G.X] : Presheaf.IsSheaf J (additivePoints G) := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{u})
  rw [isSheaf_iff_isSheaf_of_type]
  have e : additivePoints G ⋙ forget AddCommGrpCat.{u} ≅ yoneda.obj G.X :=
    NatIso.ofComponents (fun T => Equiv.toIso Additive.toMul) (fun _ => rfl)
  exact Presieve.isSheaf_iso J e.symm
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj G.X))

/-- A relative scheme over `Spec R` with affine source is isomorphic to the relative spectrum
of an `R`-algebra (its global sections). -/
theorem exists_iso_algSpec {R : CommRingCat.{u}} (T : Over (Spec R)) [IsAffine T.left] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Nonempty (T ≅ (algSpec R).obj (op (CommAlgCat.of R C))) := by
  let : T.left.Over (Spec R) := ⟨T.hom⟩
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, ⟨T.left.isoSpec.asOver (Spec R)⟩⟩

/-- Over an affine base, a morphism of Zariski sheaves of abelian groups is an isomorphism once
it is bijective on the relative spectrum of every algebra. -/
theorem isIso_of_bijective_algSpec {R : CommRingCat.{u}}
    {F G : (Over (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec R)) F)
    (hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec R)) G) (α : F ⟶ G)
    (h : ∀ (C : Type u) [CommRing C] [Algebra R C],
      Function.Bijective (α.app (op ((algSpec R).obj (op (CommAlgCat.of R C)))))) :
    IsIso α :=
  isIso_of_bijective_affine hF hG α fun T _ => by
    obtain ⟨C, _, _, ⟨e⟩⟩ := exists_iso_algSpec T
    exact bijective_app_of_iso α e (h C)

/-- Over an affine base, a morphism from the additive points of a commutative group scheme to
the characters of another is an isomorphism once it is bijective on the relative spectrum of
every algebra. -/
theorem isIso_additivePoints_characters_of_bijective {R : CommRingCat.{u}}
    {H G : CommGroupScheme (Spec R)} (α : additivePoints H.toGrp ⟶ characters G)
    (h : ∀ (C : Type u) [CommRing C] [Algebra R C],
      Function.Bijective (α.app (op ((algSpec R).obj (op (CommAlgCat.of R C)))))) :
    IsIso α :=
  isIso_of_bijective_algSpec (isSheaf_additivePoints _ H.toGrp) (isSheaf_characters G _) α h

end Local

end Langlands.GroupScheme.Cartier.FiniteDual
