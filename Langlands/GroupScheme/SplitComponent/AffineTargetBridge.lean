import Langlands.GroupScheme.SplitComponent.SchemeBridge
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.TorusActionBridge
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Torus.UniversalPoint

/-! # Natural homomorphisms into an arbitrary affine group scheme

Homomorphisms from a corepresented group scheme into an arbitrary affine group scheme `G` are
exchanged with natural homomorphisms into the algebra points of `G`, compatibly with centrality.
The lattice-torus model of the split torus has the expected unit coordinates, and a split
component absorbs every central homomorphism from a split torus.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitComponent

section AffineTarget

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- The algebra points of an affine group scheme are the points of its coordinate model. -/
def coordinatePointsEquiv (S : CommAlgCat.{u} R) :
    G.affinePoints S ≃* (AffineCoordinates.functor G).obj S :=
  (isoPointsEquiv (AffineCoordinates.groupSchemeIso G).symm ((algSpec R).obj (op S))).trans
    (Corepresented.affinePointsEquiv (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G) S)

theorem coordinatePointsEquiv_naturality {S S' : CommAlgCat.{u} R} (a : S ⟶ S')
    (y : G.affinePoints S) :
    coordinatePointsEquiv G S' (G.affinePointMap a y) =
      (AffineCoordinates.functor G).map a (coordinatePointsEquiv G S y) := by
  change Corepresented.affinePointsEquiv _ _ S'
      (((algSpec R).map a.op ≫ y) ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom) =
    (AffineCoordinates.functor G).map a (Corepresented.affinePointsEquiv _ _ S
      (y ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom))
  rw [Category.assoc]
  exact Corepresented.affinePointsEquiv_naturality _ _ a _

/-- The coordinate comparison is natural in the test algebra. -/
def coordinatePointsTrans : G.affinePointFunctor ⟶ AffineCoordinates.functor G where
  app S := GrpCat.ofHom (coordinatePointsEquiv G S).toMonoidHom
  naturality S S' a := by
    ext y
    exact coordinatePointsEquiv_naturality G a y

variable {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A natural homomorphism into the algebra points of `G` gives a homomorphism of group schemes. -/
def homOfNat (β : F ⟶ G.affinePointFunctor) : Corepresented.groupScheme F e ⟶ G :=
  Corepresented.groupSchemeMap e (AffineCoordinates.corepresentation G)
      (β ≫ coordinatePointsTrans G) ≫ (AffineCoordinates.groupSchemeIso G).hom

/-- The homomorphism induced by `β` acts on algebra points by `β`. -/
theorem homOfNat_affinePoints (β : F ⟶ G.affinePointFunctor) (S : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op S) ⟶ (Corepresented.groupScheme F e).X) :
    x ≫ (homOfNat G e β).hom.hom = β.app S (Corepresented.affinePointsEquiv F e S x) := by
  set p : G.affinePoints S := β.app S (Corepresented.affinePointsEquiv F e S x) with hp
  have h := Corepresented.groupSchemeMap_affinePoints e (AffineCoordinates.corepresentation G)
    (β ≫ coordinatePointsTrans G) x
  have h' : x ≫ (Corepresented.groupSchemeMap e (AffineCoordinates.corepresentation G)
      (β ≫ coordinatePointsTrans G)).hom.hom =
        p ≫ (AffineCoordinates.groupSchemeIso G).inv.hom.hom :=
    (Corepresented.affinePointsEquiv _ _ S).injective h
  change x ≫ (Corepresented.groupSchemeMap e (AffineCoordinates.corepresentation G)
      (β ≫ coordinatePointsTrans G)).hom.hom ≫ (AffineCoordinates.groupSchemeIso G).hom.hom.hom = p
  have hy : (AffineCoordinates.groupSchemeIso G).inv.hom.hom ≫
      (AffineCoordinates.groupSchemeIso G).hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  rw [← Category.assoc, h', Category.assoc, hy, Category.comp_id]

/-- Centrality of `β` gives centrality of the induced homomorphism. -/
theorem isCentral_homOfNat {β : F ⟶ G.affinePointFunctor} (hβ : IsCentralNat β) :
    IsCentral (homOfNat G e β) := by
  apply IsCentral.comp_iso
  apply isCentral_groupSchemeMap
  intro S x y
  obtain ⟨y, rfl⟩ := (coordinatePointsEquiv G S).surjective y
  exact (hβ S x y).map (coordinatePointsEquiv G S)

variable {G} in
/-- The algebra points of a homomorphism out of a corepresented group scheme. -/
def natToPoints (h : Corepresented.groupScheme F e ⟶ G) : F ⟶ G.affinePointFunctor where
  app S := GrpCat.ofHom (((Corepresented.groupScheme F e).affinePointsTarget h S).comp
    (Corepresented.affinePointsEquiv F e S).symm.toMonoidHom)
  naturality S S' a := by
    ext χ
    change (Corepresented.affinePointsEquiv F e S').symm (F.map a χ) ≫ h.hom.hom =
      (algSpec R).map a.op ≫ (Corepresented.affinePointsEquiv F e S).symm χ ≫ h.hom.hom
    rw [← Category.assoc]
    congr 1
    apply (Corepresented.affinePointsEquiv F e S').injective
    rw [MulEquiv.apply_symm_apply, Corepresented.affinePointsEquiv_naturality,
      MulEquiv.apply_symm_apply]

omit [IsAffine G.X.left] in
variable {G} in
theorem natToPoints_app (h : Corepresented.groupScheme F e ⟶ G) (S : CommAlgCat.{u} R)
    (χ : F.obj S) :
    (natToPoints e h).app S χ = (Corepresented.affinePointsEquiv F e S).symm χ ≫ h.hom.hom :=
  rfl

omit [IsAffine G.X.left] in
variable {G} in
/-- A central homomorphism has central algebra points. -/
theorem isCentralNat_natToPoints {h : Corepresented.groupScheme F e ⟶ G} (hc : IsCentral h) :
    IsCentralNat (natToPoints e h) :=
  fun S χ y => commute_of_mem_center (hc _ ((Corepresented.affinePointsEquiv F e S).symm χ)) y

end AffineTarget

section Torus

variable (R : CommRingCat.{u}) (I : Type u) [Finite I]

/-- The lattice model of the split torus has the expected unit coordinates. -/
theorem algebraPointsEquiv_torusIso (A : CommAlgCat.{u} R)
    (x : (algSpec R).obj (op A) ⟶
      (Corepresented.groupScheme (latticeFunctor R (FreeAbelianGroup I))
        (latticeCorep R (FreeAbelianGroup I))).X) :
    splitTorus.algebraPointsEquiv I A (x ≫ (torusIso R I).hom.hom.hom) =
      freeCharEquiv R I A (Corepresented.affinePointsEquiv _ _ A x) := by
  have key : splitTorus.pointsEquiv I ((algSpec R).obj (op A))
      (x ≫ (torusIso R I).hom.hom.hom) =
        freeCharEquiv R I ((algΓ R).obj ((algSpec R).obj (op A))).unop
          (Corepresented.pointsEquiv _ (latticeCorep R (FreeAbelianGroup I))
            ((algSpec R).obj (op A)) x) := by
    rw [torusIso, isoOfPointModels_hom]
    · rfl
    · intro T T' a y
      change freeCharEquiv R I _
        (Corepresented.pointsEquiv _ (latticeCorep R (FreeAbelianGroup I)) _ (a ≫ y)) = _
      rw [Corepresented.pointsEquiv_naturality]
      rfl
    · intro T T' a y
      exact splitTorus.pointsEquiv_naturality I a y
  rw [Corepresented.pointsEquiv_eq_affinePointsEquiv] at key
  funext i
  apply Units.ext
  have hi := congrArg (fun t => ((t i : (Γ(((algSpec R).obj (op A)).left, ⊤))ˣ) :
    Γ(((algSpec R).obj (op A)).left, ⊤))) key
  simp only at hi
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((splitTorus.pointsEquiv I ((algSpec R).obj (op A)) (x ≫ (torusIso R I).hom.hom.hom) i :
        Γ(((algSpec R).obj (op A)).left, ⊤))) = _
  rw [hi]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Corepresented.affineSectionsIso A).inv.hom
        ((asChar (Corepresented.affinePointsEquiv _ (latticeCorep R (FreeAbelianGroup I)) A x)
          (Multiplicative.ofAdd (FreeAbelianGroup.of i)) : A))) = _
  have hinv := Corepresented.affineSectionsIso_inv_ringHom A
  have h2 := congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (f
    ((asChar (Corepresented.affinePointsEquiv _ (latticeCorep R (FreeAbelianGroup I)) A x)
      (Multiplicative.ofAdd (FreeAbelianGroup.of i)) : A)))) hinv
  simp only at h2
  have h3 (z : CommRingCat.of A) : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom z) = z := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact h2.trans ((h3 _).trans rfl)

end Torus

end Langlands.GroupScheme.SplitComponent

namespace Langlands.GroupScheme

section Factor

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]

/-- A split component absorbs every central homomorphism from a split torus. -/
theorem IsSplitComponent.exists_comp_eq_of_isCentral
    (hfin : Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.algebra G))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G} (hi : IsSplitComponent i)
    {D : GroupScheme (Spec (CommRingCat.of k))} (φ : D ⟶ G) (hD : IsSplitTorus D)
    (hφ : IsCentral φ) : ∃ f : D ⟶ A.toGrp, f ≫ i = φ := by
  obtain ⟨I, hI, ⟨eD⟩⟩ := hD
  obtain ⟨B, j, hj, huniv⟩ := exists_largestCentralSplitTorus G hfin
  obtain ⟨g, hg⟩ := huniv A i hi.1.1.1 hi.1.2
  have : IsIso g := hi.2 B j hj g hg
  obtain ⟨g', hg'⟩ := huniv (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) (eD.inv ≫ φ)
    (isSplitTorus_splitTorus I) (hφ.comp eD.inv)
  refine ⟨eD.hom ≫ g' ≫ inv g, ?_⟩
  rw [Category.assoc, Category.assoc, ← hg, IsIso.inv_hom_id_assoc, hg', Iso.hom_inv_id_assoc]

end Factor

end Langlands.GroupScheme
