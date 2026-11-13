import Langlands.GroupScheme.Descent.SquareSemilinear
import Langlands.GroupScheme.Descent.SemilinearSolution
import Langlands.GroupScheme.IntegralModel.GenericSolutionDescent
import Langlands.GroupScheme.Descent.GaloisHom
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Semilinear generic comparison of actual integral descent solutions -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent

variable {B S U V : Scheme.{u}}

/-- The comparison induced by an upstairs isomorphism and a commuting square. -/
def squareSolutionComparison
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) {X : GroupScheme B} {H : GroupScheme S}
    {G : GroupScheme U} (t : (baseChange b).obj X ≅ H)
    (n : (baseChange c).obj H ≅ (baseChange e).obj G) :
    (baseChange e).obj ((baseChange d).obj X) ≅ (baseChange e).obj G :=
  (squareComparison b c d e h X).symm ≪≫ (baseChange c).mapIso t ≪≫ n

/-- Semilinear transport of both supplied isomorphisms gives canonical
semilinear transport of the comparison over the bottom generic base. -/
theorem squareSolutionComparison_semilinear
    (b : S ⟶ B) (c : V ⟶ S) (d : U ⟶ B) (e : V ⟶ U)
    (h : c ≫ b = e ≫ d) {X : GroupScheme B} {H : GroupScheme S}
    {G : GroupScheme U} (t : (baseChange b).obj X ≅ H)
    (n : (baseChange c).obj H ≅ (baseChange e).obj G)
    (a : S ⟶ S) (ha : a ≫ b = b) (v : V ⟶ V) (hv : v ≫ e = e)
    (hvc : v ≫ c = c ≫ a) (E : (baseChange a).obj H ≅ H)
    (ht : (baseChange a).map t.hom ≫ E.hom =
      (descentBaseChangeIso b a ha X).hom ≫ t.hom)
    (hn : (baseChange v).map n.hom ≫ (descentBaseChangeIso e v hv G).hom =
      (squareComparison c v a c hvc H).hom ≫ (baseChange c).map E.hom ≫ n.hom) :
    (baseChange v).map (squareSolutionComparison b c d e h t n).hom ≫
        (descentBaseChangeIso e v hv G).hom =
      (descentBaseChangeIso e v hv ((baseChange d).obj X)).hom ≫
        (squareSolutionComparison b c d e h t n).hom := by
  have hc := congrArg (fun f => f ≫ (squareComparison b c d e h X).inv)
    (squareComparison_semilinear b c d e h a ha v hv hvc X)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  simp only [squareSolutionComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn, squareComparison_naturality_assoc]
  rw [← Category.assoc ((baseChange c).map ((baseChange a).map t.hom))
    ((baseChange c).map E.hom) n.hom, ← Functor.map_comp, ht, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (squareComparison c v a c hvc ((baseChange b).obj X)).hom
    ((baseChange c).map (descentBaseChangeIso b a ha X).hom), ← hc]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id]
  rw [(baseChange v).map_id]
  simp only [Category.id_comp, Category.assoc]

end Langlands.GroupScheme.Descent

namespace Langlands.GroupScheme.IntegralModel

open Descent

/-- An actual integral model makes its specified generic group affine. -/
theorem genericGroup_isAffineHom
    {A L : Type u} [CommRing A] [IsDomain A] [Field L]
    [Algebra A L] [IsFractionRing A L]
    {H : GroupScheme (Spec (CommRingCat.of L))} (N : IntegralModel A L H) :
    IsAffineHom H.X.hom := by
  let : IsAffineHom N.genericFibre.X.hom :=
    MorphismProperty.pullback_snd _ _ N.affine
  rw [← Over.w N.genericIso.inv.hom.hom]
  infer_instance

/-- Affineness of a specified scalar extension descends to the original group. -/
theorem affine_of_baseChanged_integralModel
    {K L A : Type u} [Field K] [Field L] [CommRing A] [IsDomain A]
    [Algebra K L] [Algebra A L] [IsFractionRing A L]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (N : IntegralModel A L ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G)) :
    IsAffineHom G.X.hom := by
  have h : IsAffineHom (pullback.snd G.X.hom (Spec.algebraMap K L)) :=
    genericGroup_isAffineHom N
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := G.X.hom) (g := Spec.algebraMap K L)
    ⟨⟨(fieldExtension_fpqc K L).1, (fieldExtension_fpqc K L).2.1⟩,
      (fieldExtension_fpqc K L).2.2⟩ h

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {A L : Type u} [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {N : IntegralModel A L ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G)}
  {D : Datum (Spec.algebraMap R A) N.group}
  (s : Solution D)
  [Surjective (Spec.algebraMap R A)] [Flat (Spec.algebraMap R A)]
  [IsAffine s.obj.X.left]

omit [IsDomain R] [IsFractionRing R K] [IsDomain A] [IsFractionRing A L]
  [Surjective (Spec.algebraMap R A)] [Flat (Spec.algebraMap R A)] in
/-- The two coefficient towers give the same scheme map. -/
theorem solutionCoefficientSquare :
    Spec.algebraMap A L ≫ Spec.algebraMap R A =
      Spec.algebraMap K L ≫ Spec.algebraMap R K := by
  calc
    _ = Spec.algebraMap R L := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply R A L x).symm
    _ = _ := by
      symm
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact (IsScalarTower.algebraMap_apply R K L x).symm

/-- The actual model coefficient comparison equals the square comparison. -/
theorem solutionModel_baseChangeGenericIso (hN : N.IsSmooth) :
    (solutionModel s hN).baseChangeGenericIso A L =
      squareComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap R K) (Spec.algebraMap K L)
        (solutionCoefficientSquare (R := R) (K := K) (A := A) (L := L)) s.obj := by
  apply Iso.ext
  apply hom_ext_pullback_tower (Spec.algebraMap R K) (Spec.algebraMap K L) s.obj
  calc
    _ = pullback.fst ((GroupScheme.baseChange (Spec.algebraMap R A)).obj s.obj).X.hom
        (Spec.algebraMap A L) ≫ pullback.fst s.obj.X.hom (Spec.algebraMap R A) := by
      have hp := (solutionModel s hN).baseChangeGenericIso_hom_fst A L
      simp only [solutionModel, Iso.refl_inv, Grp.id_hom_hom, Over.id_left,
        Category.id_comp] at hp
      exact hp
    _ = _ := (squareComparison_hom_fst_fst _ _ _ _ _ s.obj).symm

/-- Identify the prescribed comparison with the general square construction. -/
theorem solutionGenericComparison_eq_square (hN : N.IsSmooth) :
    solutionGenericComparison s hN =
      squareSolutionComparison (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap R K) (Spec.algebraMap K L)
        (solutionCoefficientSquare (R := R) (K := K) (A := A) (L := L))
        s.iso N.genericIso := by
  simp only [solutionGenericComparison, squareSolutionComparison,
    solutionModel_baseChangeGenericIso]

/-- Actual integral and generic semilinear laws imply canonical semilinearity
of the prescribed generic comparison. -/
theorem solutionGenericComparison_semilinear (hN : N.IsSmooth)
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
    (ha : a ≫ Spec.algebraMap R A = Spec.algebraMap R A)
    (v : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
    (hv : v ≫ Spec.algebraMap K L = Spec.algebraMap K L)
    (hvc : v ≫ Spec.algebraMap A L = Spec.algebraMap A L ≫ a)
    (E : (GroupScheme.baseChange a).obj N.group ≅ N.group)
    (hs : (GroupScheme.baseChange a).map s.iso.hom ≫ E.hom =
      (descentBaseChangeIso (Spec.algebraMap R A) a ha s.obj).hom ≫ s.iso.hom)
    (hn : (GroupScheme.baseChange v).map N.genericIso.hom ≫
        (descentBaseChangeIso (Spec.algebraMap K L) v hv G).hom =
      (squareComparison (Spec.algebraMap A L) v a (Spec.algebraMap A L)
        hvc N.group).hom ≫ (GroupScheme.baseChange (Spec.algebraMap A L)).map E.hom ≫
          N.genericIso.hom) :
    (GroupScheme.baseChange v).map (solutionGenericComparison s hN).hom ≫
        (descentBaseChangeIso (Spec.algebraMap K L) v hv G).hom =
      (descentBaseChangeIso (Spec.algebraMap K L) v hv
        ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj)).hom ≫
          (solutionGenericComparison s hN).hom := by
  rw [solutionGenericComparison_eq_square]
  exact squareSolutionComparison_semilinear _ _ _ _ _ s.iso N.genericIso
    a ha v hv hvc E hs hn

/-- A normalized component of the actual integral datum supplies the integral
semilinear law needed for generic transport. -/
theorem solutionGenericComparison_semilinear_of_component (hN : N.IsSmooth)
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
    (ha : a ≫ Spec.algebraMap R A = Spec.algebraMap R A)
    (v : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
    (hv : v ≫ Spec.algebraMap K L = Spec.algebraMap K L)
    (hvc : v ≫ Spec.algebraMap A L = Spec.algebraMap A L ≫ a)
    (E : (GroupScheme.baseChange a).obj N.group ≅ N.group)
    (q : Spec (CommRingCat.of A) ⟶ Overlap (Spec.algebraMap R A))
    (hf : q ≫ fst (Spec.algebraMap R A) = 𝟙 _)
    (hg : q ≫ snd (Spec.algebraMap R A) = a)
    (he : pullIso q hf hg D.overlap = semilinearComponent N.group E)
    (hn : (GroupScheme.baseChange v).map N.genericIso.hom ≫
        (descentBaseChangeIso (Spec.algebraMap K L) v hv G).hom =
      (squareComparison (Spec.algebraMap A L) v a (Spec.algebraMap A L)
        hvc N.group).hom ≫ (GroupScheme.baseChange (Spec.algebraMap A L)).map E.hom ≫
          N.genericIso.hom) :
    (GroupScheme.baseChange v).map (solutionGenericComparison s hN).hom ≫
        (descentBaseChangeIso (Spec.algebraMap K L) v hv G).hom =
      (descentBaseChangeIso (Spec.algebraMap K L) v hv
        ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj)).hom ≫
          (solutionGenericComparison s hN).hom :=
  solutionGenericComparison_semilinear s hN a ha v hv hvc E
    (s.semilinear a ha q hf hg E he) hn

/-- Canonical Galois compatibility of the actual generic comparison. -/
def SolutionGenericGaloisCompatible (hN : N.IsSmooth) : Prop :=
  ∀ σ : L ≃ₐ[K] L,
    (GroupScheme.baseChange (galoisBaseMap K L σ)).map
          (solutionGenericComparison s hN).hom ≫
        (descentBaseChangeIso (Spec.algebraMap K L) (galoisBaseMap K L σ)
          (galoisBaseMap_over K L σ) G).hom =
      (descentBaseChangeIso (Spec.algebraMap K L) (galoisBaseMap K L σ)
        (galoisBaseMap_over K L σ)
        ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj)).hom ≫
          (solutionGenericComparison s hN).hom

/-- Actual integral semilinear laws give Galois compatibility of the generic
comparison. -/
theorem solutionGenericGaloisCompatible_of_semilinear (hN : N.IsSmooth)
    (a : (L ≃ₐ[K] L) → (Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A)))
    (ha : ∀ σ, a σ ≫ Spec.algebraMap R A = Spec.algebraMap R A)
    (hvc : ∀ σ, galoisBaseMap K L σ ≫ Spec.algebraMap A L =
      Spec.algebraMap A L ≫ a σ)
    (E : ∀ σ, (GroupScheme.baseChange (a σ)).obj N.group ≅ N.group)
    (hs : ∀ σ, (GroupScheme.baseChange (a σ)).map s.iso.hom ≫ (E σ).hom =
      (descentBaseChangeIso (Spec.algebraMap R A) (a σ) (ha σ) s.obj).hom ≫ s.iso.hom)
    (hn : ∀ σ, (GroupScheme.baseChange (galoisBaseMap K L σ)).map N.genericIso.hom ≫
        (descentBaseChangeIso (Spec.algebraMap K L) (galoisBaseMap K L σ)
          (galoisBaseMap_over K L σ) G).hom =
      (squareComparison (Spec.algebraMap A L) (galoisBaseMap K L σ) (a σ)
        (Spec.algebraMap A L) (hvc σ) N.group).hom ≫
          (GroupScheme.baseChange (Spec.algebraMap A L)).map (E σ).hom ≫
            N.genericIso.hom) : SolutionGenericGaloisCompatible s hN := by
  intro σ
  exact solutionGenericComparison_semilinear s hN (a σ) (ha σ)
    (galoisBaseMap K L σ) (galoisBaseMap_over K L σ) (hvc σ) (E σ) (hs σ) (hn σ)

variable [IsGalois K L]

/-- Descend the actual Galois-compatible generic comparison, without a
finiteness hypothesis on the Galois extension. -/
def solutionGaloisGenericIso (hN : N.IsSmooth)
    (hc : SolutionGenericGaloisCompatible s hN) :
    (GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj ≅ G := by
  let : IsAffineHom G.X.hom := affine_of_baseChanged_integralModel N
  let : IsAffineHom ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd s.obj.X.hom (Spec.algebraMap R K)))
  exact GaloisHom.iso (solutionGenericComparison s hN).hom hc

/-- The descended generic isomorphism recovers the prescribed comparison exactly. -/
theorem baseChange_solutionGaloisGenericIso (hN : N.IsSmooth)
    (hc : SolutionGenericGaloisCompatible s hN) :
    (GroupScheme.baseChange (Spec.algebraMap K L)).mapIso
      (solutionGaloisGenericIso s hN hc) = solutionGenericComparison s hN := by
  let : IsAffineHom G.X.hom := affine_of_baseChanged_integralModel N
  let : IsAffineHom ((GroupScheme.baseChange (Spec.algebraMap R K)).obj s.obj).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd s.obj.X.hom (Spec.algebraMap R K)))
  apply Iso.ext
  exact GaloisHom.baseChange_iso_hom (solutionGenericComparison s hN).hom hc

/-- A Galois-compatible affine solution gives a smooth model of the prescribed
original generic group. -/
def ofGaloisCompatibleSolution (hN : N.IsSmooth)
    (hc : SolutionGenericGaloisCompatible s hN) : IntegralModel R K G :=
  ofAffineSolution s hN (solutionGaloisGenericIso s hN hc)

theorem isSmooth_ofGaloisCompatibleSolution (hN : N.IsSmooth)
    (hc : SolutionGenericGaloisCompatible s hN) :
    (ofGaloisCompatibleSolution s hN hc).IsSmooth :=
  isSmooth_ofAffineSolution s hN _

/-- The resulting model recovers the upstairs model over the identity of the
prescribed generic group. -/
def isoOfGaloisCompatibleSolution (hN : N.IsSmooth)
    (hc : SolutionGenericGaloisCompatible s hN) :
    ((ofGaloisCompatibleSolution s hN hc).baseChange A L).Iso N (Iso.refl _) :=
  isoOfSolutionGenericRecovery s hN _ (baseChange_solutionGaloisGenericIso s hN hc)

end Langlands.GroupScheme.IntegralModel
