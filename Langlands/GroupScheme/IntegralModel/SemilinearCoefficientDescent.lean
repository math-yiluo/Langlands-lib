import Langlands.GroupScheme.IntegralModel.TwistCoefficientComparison
import Langlands.GroupScheme.IntegralModel.GenericCoefficientDescent

/-! # Descent of semilinear isomorphisms to supplied coefficient models -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

@[reassoc] private theorem map_fst {S T : Scheme.{u}} (c : T ⟶ S)
    {G H : GroupScheme S} (f : G ⟶ H) :
    ((baseChange c).map f).hom.hom.left ≫ pullback.fst H.X.hom c =
      pullback.fst G.X.hom c ≫ f.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- A canonical tower comparison intertwines the canonical semilinear
isomorphisms on the two generic pullback presentations. -/
theorem pullbackComparison_semilinear {B S T : Scheme.{u}}
    (b : S ⟶ B) (c : T ⟶ S) (d : T ⟶ B) (h : c ≫ b = d)
    (a : S ⟶ S) (ha : a ≫ b = b) (v : T ⟶ T) (hv : v ≫ d = d)
    (hvc : v ≫ c = c ≫ a) (G : GroupScheme B) :
    (baseChange v).map (pullbackComparison b c d h G).hom ≫
        (descentBaseChangeIso d v hv G).hom =
      (squareComparison c v a c hvc ((baseChange b).obj G)).hom ≫
        (baseChange c).map (descentBaseChangeIso b a ha G).hom ≫
          (pullbackComparison b c d h G).hom := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      descentBaseChangeIso_hom_fst, pullbackComparison_hom_fst]
    conv_lhs =>
      erw [map_fst_assoc v (pullbackComparison b c d h G).hom (pullback.fst G.X.hom d)]
      rw [pullbackComparison_hom_fst]
    conv_rhs =>
      erw [map_fst_assoc c (descentBaseChangeIso b a ha G).hom (pullback.fst G.X.hom b)]
      rw [descentBaseChangeIso_hom_fst]
      erw [squareComparison_hom_fst_fst_assoc c v a c hvc ((baseChange b).obj G)
        (pullback.fst G.X.hom b)]
  · exact (Over.w _).trans (Over.w _).symm

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.IntegralModel
open Descent

section Operations

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H J : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {P : IntegralModel R K J}
  {f : G ≅ H} {g : H ≅ J}

/-- Compose compatible actual integral-model isomorphisms. -/
def Iso.trans (e : M.Iso N f) (d : N.Iso P g) : M.Iso P (f ≪≫ g) where
  iso := e.iso ≪≫ d.iso
  generic_comm := by
    simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [d.generic_comm, ← Category.assoc, e.generic_comm, Category.assoc]

/-- Reverse a compatible actual integral-model isomorphism. -/
def Iso.symm (e : M.Iso N f) : N.Iso M f.symm where
  iso := e.iso.symm
  generic_comm := by
    simp only [CategoryTheory.Iso.symm_hom]
    apply (cancel_epi ((GroupScheme.baseChange (Spec.algebraMap R K)).map e.iso.hom)).mp
    calc
      _ = M.genericIso.hom := by
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, e.iso.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.id_comp]
      _ = _ := by
        rw [← Category.assoc, e.generic_comm, Category.assoc, f.hom_inv_id, Category.comp_id]

/-- Change the named generic isomorphism along equality of its forward map. -/
def Iso.changeGeneric (e : M.Iso N f) (f' : G ≅ H) (h : f.hom = f'.hom) : M.Iso N f' where
  iso := e.iso
  generic_comm := e.generic_comm.trans (congrArg (fun k => M.genericIso.hom ≫ k) h)

variable
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (hvc : v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)

/-- Twist a compatible integral model homomorphism by the same coefficient square. -/
def Hom.twist {f : G ⟶ H} (e : M.Hom N f) :
    (M.twist a v hvc).Hom (N.twist a v hvc) ((GroupScheme.baseChange v).map f) where
  hom := (GroupScheme.baseChange a).map e.hom
  generic_comm := by
    apply (cancel_epi (squareComparison (Spec.algebraMap R K) v a
      (Spec.algebraMap R K) hvc M.group).hom).mp
    simp only [IntegralModel.twist, CategoryTheory.Iso.trans_hom,
      CategoryTheory.Iso.symm_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
    rw [← squareComparison_naturality_assoc (Spec.algebraMap R K) v a
      (Spec.algebraMap R K) hvc e.hom]
    simp only [CategoryTheory.Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.Functor.map_comp, e.generic_comm, CategoryTheory.Functor.map_comp]

/-- Twist a compatible actual model isomorphism, retaining its generic map. -/
def Iso.twist (e : M.Iso N f) :
    (M.twist a v hvc).Iso (N.twist a v hvc) ((GroupScheme.baseChange v).mapIso f) where
  iso := (GroupScheme.baseChange a).mapIso e.iso
  generic_comm := (e.toHom.twist a v hvc).generic_comm

end Operations

section Coefficients

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} (N : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  (a : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))
  (v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (hvc : v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a)
  (a' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
  (v' : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
  (hvq : v' ≫ Spec.algebraMap A L = Spec.algebraMap A L ≫ a')
  (ha : a' ≫ Spec.algebraMap R A = Spec.algebraMap R A ≫ a)
  (hv : v' ≫ Spec.algebraMap K L = Spec.algebraMap K L ≫ v)
  {H : GroupScheme (Spec (CommRingCat.of L))} (P : IntegralModel A L H)
  (η : (GroupScheme.baseChange (Spec.algebraMap K L)).obj G ≅ H)
  (e : (N.baseChange A L).Iso P η)
  (f : (GroupScheme.baseChange v).obj G ≅ G)
  (f' : (GroupScheme.baseChange v').obj H ≅ H)
  (φ : (P.twist a' v' hvq).Iso P f')

/-- The generic isomorphism induced by conjugating an upstairs semilinear
map through a supplied finite-coefficient recovery isomorphism. -/
def coefficientSemilinearGenericIso :=
  (((squareComparison (Spec.algebraMap K L) v' v (Spec.algebraMap K L) hv G).symm ≪≫
      (GroupScheme.baseChange v').mapIso η) ≪≫ f') ≪≫ η.symm

/-- Actual conjugation through coefficient/twist comparison and model recovery. -/
def coefficientSemilinearIso :
    ((N.twist a v hvc).baseChange A L).Iso (N.baseChange A L)
      (coefficientSemilinearGenericIso (G := G) L v v' hv η f') :=
  ((((N.twistBaseChangeIso A L a v hvc a' v' hvq ha hv).symm.trans
    (e.twist a' v' hvq)).trans φ).trans e.symm)

variable (hgeneric : (GroupScheme.baseChange v').map η.hom ≫ f'.hom =
    (squareComparison (Spec.algebraMap K L) v' v (Spec.algebraMap K L) hv G).hom ≫
      (GroupScheme.baseChange (Spec.algebraMap K L)).map f.hom ≫ η.hom)

/-- Relabel the actual upstairs conjugate by the specified scalar extension
of the downstairs generic map. -/
def coefficientSemilinearIsoOver :
    ((N.twist a v hvc).baseChange A L).Iso (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f) := by
  let u := coefficientSemilinearIso N A L a v hvc a' v' hvq ha hv P η e f' φ
  have hu : (coefficientSemilinearGenericIso (G := G) L v v' hv η f').hom =
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f).hom := by
    have hg := congrArg (fun g => g ≫ η.inv) hgeneric
    simp only [Category.assoc, CategoryTheory.Iso.hom_inv_id, Category.comp_id] at hg
    simp only [coefficientSemilinearGenericIso, CategoryTheory.Iso.trans_hom,
      CategoryTheory.Iso.symm_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc]
    rw [hg, CategoryTheory.Iso.inv_hom_id_assoc]
  exact u.changeGeneric ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f) hu

variable [Flat (Spec.algebraMap R A)] [Surjective (Spec.algebraMap R A)]

/-- Descend an upstairs semilinear isomorphism to an existing coefficient
model when its prescribed generic map descends. -/
def semilinearIsoFromCoefficients : (N.twist a v hvc).Iso N f :=
  (coefficientSemilinearIsoOver N A L a v hvc a' v' hvq ha hv P η e f f' φ hgeneric).descendFromCoefficients A L

/-- Coefficient pullback recovers the supplied conjugate integral isomorphism. -/
theorem baseChange_semilinearIsoFromCoefficients :
    (GroupScheme.baseChange (Spec.algebraMap R A)).mapIso
        (semilinearIsoFromCoefficients N A L a v hvc a' v' hvq ha hv P η e f f' φ hgeneric).iso =
      (coefficientSemilinearIso N A L a v hvc a' v' hvq ha hv P η e f' φ).iso :=
  Iso.baseChange_descendFromCoefficients A L
    (coefficientSemilinearIsoOver N A L a v hvc a' v' hvq ha hv P η e f f' φ hgeneric)

/-- The descended actual integral map satisfies the prescribed generic
semilinear law. -/
theorem semilinearIsoFromCoefficients_generic_comm :
    (GroupScheme.baseChange v).map N.genericIso.hom ≫ f.hom =
      (squareComparison (Spec.algebraMap R K) v a (Spec.algebraMap R K) hvc N.group).hom ≫
        (GroupScheme.baseChange (Spec.algebraMap R K)).map
          (semilinearIsoFromCoefficients N A L a v hvc a' v' hvq ha hv P η e f f' φ hgeneric).iso.hom ≫
            N.genericIso.hom :=
  Hom.twist_generic_comm N a v hvc
    (semilinearIsoFromCoefficients N A L a v hvc a' v' hvq ha hv P η e f f' φ hgeneric).toHom

end Coefficients
end Langlands.GroupScheme.IntegralModel
