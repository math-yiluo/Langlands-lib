/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase
public import WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionCoherence

/-! # Exceptional tensor maps under composition and etale restriction

proof.md`, paragraph 3
(auxiliary; not a blueprint node).

All categories are ordinary unbounded etale module derived categories. We use
supplied compactifications and the graph-normalized compositor, with no qc or
Noetherian hypotheses. The exact inverse image is represented by its canonically
isomorphic total left-derived functor. All reassociation arrows are explicit.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] sfGraphCompactSupportCompIso
attribute [local instance high] SymmetricCategory.toBraidedCategory

private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G G' : D ⥤ C} (adj : F ⊣ G) (adj' : F' ⊣ G')
    (E : F ≅ F') {N : C} {K : D} (t : N ⟶ G.obj K) :
    (adj'.homEquiv N K).symm
        (t ≫ (conjugateIsoEquiv adj adj' E.symm).hom.app K) =
      E.inv.app N ≫ (adj.homEquiv N K).symm t := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change F'.map t ≫ F'.map ((conjugateEquiv adj adj' E.inv).app K) ≫
    adj'.counit.app K = _
  rw [conjugateEquiv_counit]
  rw [E.inv.naturality_assoc]

private theorem composite_transpose_post
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D}
    (adj : F ⊣ G) (adj' : F' ⊣ G') {N : C} {P : D} {K : E}
    (s : N ⟶ G.obj P) (t : P ⟶ G'.obj K) :
    ((adj.comp adj').homEquiv N K).symm (s ≫ G.map t) =
      F'.map ((adj.homEquiv N P).symm s) ≫ (adj'.homEquiv P K).symm t := by
  rw [Adjunction.comp_homEquiv]
  change (adj'.homEquiv _ _).symm ((adj.homEquiv _ _).symm (s ≫ G.map t)) = _
  rw [adj.homEquiv_naturality_right_symm, adj'.homEquiv_naturality_left_symm]

private theorem projection_composition_calculation
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Fa : C ⥤ D) (Fb : D ⥤ E) (Fh : C ⥤ E) (e : Fh ≅ Fa ⋙ Fb)
    (TY : D ⥤ D) (TZ : E ⥤ E)
    {H M DH DM D₂ D₃ : C} {V : D} {Z₀ K : E}
    (δ : H ⟶ M) (d : DH ⟶ DM) (g : DM ⟶ D₂) (r : D₂ ⟶ D₃)
    (p : Fa.obj M ⟶ V) (ep : Fa.obj D₃ ⟶ TY.obj V)
    (qH : Fh.obj DH ⟶ TZ.obj (Fh.obj H))
    (qM : Fh.obj DM ⟶ TZ.obj (Fh.obj M))
    (qa : Fa.obj D₂ ⟶ TY.obj (Fa.obj M))
    (qb : Fb.obj (TY.obj (Fa.obj M)) ⟶ TZ.obj (Fb.obj (Fa.obj M)))
    (qv : Fb.obj (TY.obj V) ⟶ TZ.obj (Fb.obj V))
    (eh : Fh.obj H ⟶ Z₀) (eb : Fb.obj V ⟶ Z₀) (ℓ : TZ.obj Z₀ ⟶ K)
    (scalar : Fh.map δ ≫ e.hom.app M ≫ Fb.map p ≫ eb = eh)
    (natd : Fh.map d ≫ qM = qH ≫ TZ.map (Fh.map δ))
    (comp : qM ≫ TZ.map (e.hom.app M) =
      e.hom.app DM ≫ Fb.map (Fa.map g) ≫ Fb.map qa ≫ qb)
    (assoc : Fa.map r ≫ ep = qa ≫ TY.map p)
    (natp : Fb.map (TY.map p) ≫ qv = qb ≫ TZ.map (Fb.map p)) :
    e.inv.app DH ≫ qH ≫ TZ.map eh ≫ ℓ =
      Fb.map (Fa.map d) ≫ Fb.map (Fa.map g) ≫ Fb.map (Fa.map r) ≫
        Fb.map ep ≫ qv ≫ TZ.map eb ≫ ℓ := by
  have hc : Fb.map (Fa.map g) ≫ Fb.map qa ≫ qb =
      e.inv.app DM ≫ qM ≫ TZ.map (e.hom.app M) := by
    apply (cancel_epi (e.hom.app DM)).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using comp.symm
  rw [← Fb.map_comp_assoc (Fa.map r), assoc, Fb.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Fb.map (TY.map p)) qv, natp]
  simp only [Category.assoc]
  rw [← Category.assoc (Fb.map (Fa.map g)) (Fb.map qa),
    ← Category.assoc (Fb.map (Fa.map g) ≫ Fb.map qa) qb]
  rw [show (Fb.map (Fa.map g) ≫ Fb.map qa) ≫ qb =
    e.inv.app DM ≫ qM ≫ TZ.map (e.hom.app M) by simpa only [Category.assoc] using hc]
  simp only [Category.assoc]
  have hn := e.inv.naturality d
  change Fb.map (Fa.map d) ≫ e.inv.app DM = e.inv.app DH ≫ Fh.map d at hn
  rw [← Category.assoc (Fb.map (Fa.map d)) (e.inv.app DM), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (Fh.map d) qM, natd]
  simp only [Category.assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ e.inv.app DH ≫ qH ≫ TZ.map t ≫ ℓ) scalar.symm

section TensorCoherence

open MonoidalCategory

variable (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] (T : Scheme.{u})

private theorem tensor_unit_action_assoc
    {W : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)}
    (e : W ⟶ 𝟙_ _) (P Q : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)) :
    (derivedTensorAssociator B T W P Q).hom ≫
        ((derivedTensor B T).map e).app (((derivedTensor B T).obj P).obj Q) ≫
        (derivedTensorLeftUnitor B T (((derivedTensor B T).obj P).obj Q)).hom =
      ((derivedTensor B T).map
        (((derivedTensor B T).map e).app P ≫ (derivedTensorLeftUnitor B T P).hom)).app Q := by
  change (MonoidalCategory.associator W P Q).hom ≫
    (e ▷ (P ⊗ Q)) ≫ (MonoidalCategory.leftUnitor (P ⊗ Q)).hom =
      (e ▷ P ≫ (MonoidalCategory.leftUnitor P).hom) ▷ Q
  rw [← MonoidalCategory.associator_naturality_left_assoc,
    MonoidalCategory.leftUnitor_tensor_hom]
  simp only [Iso.hom_inv_id_assoc, MonoidalCategory.comp_whiskerRight]

private theorem tensor_unit_action_naturality
    {W : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)}
    (e : W ⟶ 𝟙_ _)
    {P Q : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)} (t : P ⟶ Q) :
    ((derivedTensor B T).obj W).map t ≫
        ((derivedTensor B T).map e).app Q ≫ (derivedTensorLeftUnitor B T Q).hom =
      ((derivedTensor B T).map e).app P ≫ (derivedTensorLeftUnitor B T P).hom ≫ t := by
  rw [((derivedTensor B T).map e).naturality_assoc]
  change (e ▷ P) ≫ (𝟙_ _ ◁ t) ≫ (MonoidalCategory.leftUnitor Q).hom =
    (e ▷ P) ≫ (MonoidalCategory.leftUnitor P).hom ≫ t
  rw [MonoidalCategory.leftUnitor_naturality]

private theorem tensor_unit_action_reassociation
    {W : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)}
    (e : W ⟶ 𝟙_ _) (P Q R : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B))
    (μ : R ≅ ((derivedTensor B T).obj P).obj Q) :
    (derivedTensorAssociator B T W P Q).hom ≫
        ((derivedTensor B T).obj W).map μ.inv ≫
        ((derivedTensor B T).map e).app R ≫ (derivedTensorLeftUnitor B T R).hom =
      ((derivedTensor B T).map
        (((derivedTensor B T).map e).app P ≫ (derivedTensorLeftUnitor B T P).hom)).app Q ≫
          μ.inv := by
  rw [tensor_unit_action_naturality]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ μ.inv) (tensor_unit_action_assoc B T e P Q)

private theorem tensor_unit_action_transport
    {W H P Q R S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology B)}
    (e : W ⟶ 𝟙_ _) (d : H ⟶ ((derivedTensor B T).obj W).obj P)
    (γ : R ≅ Q) (μ : S ≅ ((derivedTensor B T).obj P).obj Q) :
    ((derivedTensor B T).map d).app R ≫
        ((derivedTensor B T).obj (((derivedTensor B T).obj W).obj P)).map γ.hom ≫
        (derivedTensorAssociator B T W P Q).hom ≫
        ((derivedTensor B T).obj W).map μ.inv ≫
        ((derivedTensor B T).map e).app S ≫ (derivedTensorLeftUnitor B T S).hom =
      ((derivedTensor B T).obj H).map γ.hom ≫
        ((derivedTensor B T).map
          (d ≫ ((derivedTensor B T).map e).app P ≫
            (derivedTensorLeftUnitor B T P).hom)).app Q ≫ μ.inv := by
  rw [← ((derivedTensor B T).map d).naturality_assoc]
  rw [tensor_unit_action_reassociation]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]

end TensorCoherence

section AmbientCalculus

variable (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)

private noncomputable def ambientEvaluation (P : DerivedCategoryModule A Y) :=
  sfEtaleCompactProjectionInverse A c (G.obj (constantComplex A Y)) P ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).map
      (adj.counit.app (constantComplex A Y))).app P ≫
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y P).hom

private theorem ambient_transpose (P : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        (sfEtaleAmbientTensorMap A c G adj P) ≫ adj.counit.app P =
      sfEtaleCompactProjectionInverse A c (G.obj (constantComplex A Y)) P ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map
          (adj.counit.app (constantComplex A Y))).app P ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y P).hom := by
  exact (adj.homEquiv _ _).symm_apply_apply _

private theorem ambient_naturality
    {P Q : DerivedCategoryModule A Y} (t : P ⟶ Q) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj (G.obj (constantComplex A Y))).map
        ((L(upperStar (ModuleCat.{u + 1} A) f)).map t) ≫
      sfEtaleAmbientTensorMap A c G adj Q =
    sfEtaleAmbientTensorMap A c G adj P ≫ G.map t := by
  unfold sfEtaleAmbientTensorMap
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  change (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        (G.obj (constantComplex A Y))).map
          ((L(upperStar (ModuleCat.{u + 1} A) f)).map t)) ≫
        ambientEvaluation A c G adj Q = ambientEvaluation A c G adj P ≫ t
  unfold ambientEvaluation
  rw [← Category.assoc, ← Category.assoc,
    sfEtaleCompactProjectionInverse_naturality_right]
  simp only [Category.assoc]
  erw [tensor_unit_action_naturality]

private theorem ambient_associativity_transpose
    (P Q : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((derivedTensorAssociator (ModuleCat.{u + 1} A) X
          (G.obj (constantComplex A Y))
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj P)
          ((L(upperStar (ModuleCat.{u + 1} A) f)).obj Q)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} A) X).obj
          (G.obj (constantComplex A Y))).map
            (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f P Q).inv) ≫
      ambientEvaluation A c G adj (((derivedTensor (ModuleCat.{u + 1} A) Y).obj P).obj Q) =
    sfEtaleCompactProjectionInverse A c
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          (G.obj (constantComplex A Y))).obj
            ((L(upperStar (ModuleCat.{u + 1} A) f)).obj P)) Q ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        (ambientEvaluation A c G adj P)).app Q := by
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let W := G.obj (constantComplex A Y)
  let T := derivedTensor (ModuleCat.{u + 1} A) Y
  let TX := derivedTensor (ModuleCat.{u + 1} A) X
  let U := L(upperStar (ModuleCat.{u + 1} A) f)
  let αX := derivedTensorAssociator (ModuleCat.{u + 1} A) X W (U.obj P) (U.obj Q)
  let αY := derivedTensorAssociator (ModuleCat.{u + 1} A) Y (F.obj W) P Q
  let μ := leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f P Q
  have h := sfEtaleCompactProjectionInverse_associativity A c W P Q
  have hc : F.map (αX.hom ≫ (TX.obj W).map μ.inv) ≫
      F.map ((TX.obj W).map μ.hom ≫ αX.inv) = 𝟙 _ := by
    rw [← F.map_comp]
    simp only [Category.assoc, ← Functor.map_comp_assoc, μ.inv_hom_id]
    rw [(TX.obj W).map_id, Category.id_comp, αX.hom_inv_id, F.map_id]
  have hq : F.map (αX.hom ≫ (TX.obj W).map μ.inv) ≫
      sfEtaleCompactProjectionInverse A c W ((T.obj P).obj Q) =
      sfEtaleCompactProjectionInverse A c ((TX.obj W).obj (U.obj P)) Q ≫
        (T.map (sfEtaleCompactProjectionInverse A c W P)).app Q ≫ αY.hom := by
    change sfEtaleCompactProjectionInverse A c W ((T.obj P).obj Q) ≫ αY.inv =
      F.map ((TX.obj W).map μ.hom ≫ αX.inv) ≫
        sfEtaleCompactProjectionInverse A c ((TX.obj W).obj (U.obj P)) Q ≫
          (T.map (sfEtaleCompactProjectionInverse A c W P)).app Q at h
    calc
      _ = F.map (αX.hom ≫ (TX.obj W).map μ.inv) ≫
          (sfEtaleCompactProjectionInverse A c W ((T.obj P).obj Q) ≫ αY.inv) ≫
            αY.hom := by
        dsimp only [F, T, TX, U, W, αX, αY, μ]
        simp only [Category.assoc, Iso.inv_hom_id,
          Category.comp_id]
      _ = _ := by
        rw [h]
        simp only [← Category.assoc, hc, Category.id_comp]
  change F.map (αX.hom ≫ (TX.obj W).map μ.inv) ≫
      (sfEtaleCompactProjectionInverse A c W ((T.obj P).obj Q) ≫
        (T.map (adj.counit.app (constantComplex A Y))).app ((T.obj P).obj Q) ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Y ((T.obj P).obj Q)).hom) = _
  rw [← Category.assoc, hq]
  simp only [Category.assoc]
  rw [tensor_unit_action_assoc]
  simp only [ambientEvaluation, Functor.map_comp, NatTrans.comp_app]
  rfl

end AmbientCalculus

attribute [local irreducible] sfEtaleAmbientTensorMap

/-- The counit-preserving comparison c, the adjunction conjugate of the inverse
graph-normalized compact-support compositor.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
noncomputable def sfExceptionalCompComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ca : Compactification a) (cb : Compactification b)
    (ch : Compactification (a ≫ b))
    (Ga : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (Gb : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (Gh : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adja : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca ⊣ Ga)
    (adjb : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb ⊣ Gb)
    (adjh : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch ⊣ Gh) :
    Gh ≅ Gb ⋙ Ga :=
  conjugateIsoEquiv adjh (adja.comp adjb)
    (sfGraphCompactSupportCompIso A a b ca cb ch).symm

/-- The specified morphism delta = c at the coefficient unit followed by the
inverse of theta_a at omega_b. Its data are the two specified maps.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
noncomputable def sfExceptionalCompDelta
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ca : Compactification a) (cb : Compactification b)
    (ch : Compactification (a ≫ b))
    (Ga : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (Gb : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (Gh : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adja : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca ⊣ Ga)
    (adjb : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb ⊣ Gb)
    (adjh : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch ⊣ Gh)
    (ha : ∀ P : DerivedCategoryModule A Y, IsIso (sfEtaleAmbientTensorMap A ca Ga adja P)) :
    Gh.obj (constantComplex A Z) ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj (Ga.obj (constantComplex A Y))).obj
        ((L(upperStar (ModuleCat.{u + 1} A) a)).obj (Gb.obj (constantComplex A Z))) :=
  letI := ha (Gb.obj (constantComplex A Z))
  (sfExceptionalCompComparison A a b ca cb ch Ga Gb Gh adja adjb adjh).hom.app
      (constantComplex A Z) ≫
    inv (sfEtaleAmbientTensorMap A ca Ga adja (Gb.obj (constantComplex A Z)))

/-- The canonical reassociation from (W tensor a*V) tensor (ba)*K to
W tensor a*(V tensor b*K), using pullback composition, tensor associativity
and the inverse of the canonical oplax pullback tensor comparison.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
noncomputable def sfExceptionalTensorReassociation
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (W : DerivedCategoryModule A X) (V : DerivedCategoryModule A Y)
    (K : DerivedCategoryModule A Z) :
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj W).obj
        ((L(upperStar (ModuleCat.{u + 1} A) a)).obj V))).obj
          ((L(upperStar (ModuleCat.{u + 1} A) (a ≫ b))).obj K) ⟶
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj W).obj
      ((L(upperStar (ModuleCat.{u + 1} A) a)).obj
        (((derivedTensor (ModuleCat.{u + 1} A) Y).obj V).obj
          ((L(upperStar (ModuleCat.{u + 1} A) b)).obj K))) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj _).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a b).hom.app K) ≫
    (derivedTensorAssociator (ModuleCat.{u + 1} A) X W
      ((L(upperStar (ModuleCat.{u + 1} A) a)).obj V)
      ((L(upperStar (ModuleCat.{u + 1} A) a)).obj
        ((L(upperStar (ModuleCat.{u + 1} A) b)).obj K))).hom ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj W).map
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a V
        ((L(upperStar (ModuleCat.{u + 1} A) b)).obj K)).inv

/-- The canonical composition identity, its specified scalar isomorphism, and the
stated invertibility consequence.

Proof plan (the eight steps of the node):
1. Normalize compact support by the graph compositor. Its conjugate is c, so the
   transported counit is the composite counit (def-weil-pbc-composite-adjunction).
   Write phi_f = inverse projection followed by counit tensor identity and unitor
   (lem-sf-etale-ambient-adjoint-projection, lem-kun-tensor-unit).
2. Put M = omega_a tensor a*omega_b, s = theta_a(omega_b), d = c_A inverse s.
   The transpose of s is phi_a(omega_b). Consequently the scalar composite
   counit evaluated on d is epsilon_b followed after F_b(phi_a(omega_b)).
   Both c_A and s are invertible, proving delta is invertible.
3. Naturality of theta_a follows by transposing and counit naturality. The
   iterated tensor map has composite transpose phi_b(K) F_b(phi_a(omega_b tensor b*K)).
4. Projection associativity (lem-sf-etale-compact-projection-coherence) rewrites
   phi_a(omega_b tensor b*K) as (phi_a(omega_b) tensor identity) q_a(M,b*K).
   Naturality of q_b then combines its scalar counits.
5. Projection/compositor coherence replaces the two inverse projections by q_h.
   The scalar counit equality in step 2 identifies this with the transpose of
   c_K theta_h(K) (d tensor identity). Injectivity of the composite Hom bijection
   gives equality of the actual maps. Cancel d tensor identity to get the formula.
   Insert precisely the pullback composition, associator and tensor comparison
   of lem-kun-inverse-image-monoidal, as in sfExceptionalTensorReassociation.
6. Every factor on the right is invertible if theta_b(K) is, so theta_h(K) is.
   The tensor-invertibility hypothesis on omega_b is retained as stated, though
   it is unnecessary under the universal hypothesis on theta_a.
7. For separated etale a, let rho be the normalized comparison of
   lem-sf-etale-unit-tensor-arbitrary-base. Then lambda = rho inverse c inverse,
   and the scalar normalization identifies lambda_A inverse with the unit action
   composed with delta.
8. Apply rho to step 5. Naturality of the unitors cancels the omega_a unit;
   compose with lambda_K and lambda_A tensor identity to obtain the restriction
   equation below. No boundedness, constructibility, qc or Noetherian input occurs.

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
theorem sfExceptionalTensorTransitivity
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ca : Compactification a) (cb : Compactification b)
    (ch : Compactification (a ≫ b))
    (Ga : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (Gb : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (Gh : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adja : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca ⊣ Ga)
    (adjb : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb ⊣ Gb)
    (adjh : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch ⊣ Gh)
    (ha : ∀ P : DerivedCategoryModule A Y, IsIso (sfEtaleAmbientTensorMap A ca Ga adja P)) :
    IsIso (sfExceptionalCompDelta A a b ca cb ch Ga Gb Gh adja adjb adjh ha) ∧
      (∀ K : DerivedCategoryModule A Z,
        sfEtaleAmbientTensorMap A ch Gh adjh K ≫
            (sfExceptionalCompComparison A a b ca cb ch Ga Gb Gh adja adjb adjh).hom.app K =
          ((derivedTensor (ModuleCat.{u + 1} A) X).map
            (sfExceptionalCompDelta A a b ca cb ch Ga Gb Gh adja adjb adjh ha)).app
              ((L(upperStar (ModuleCat.{u + 1} A) (a ≫ b))).obj K) ≫
          sfExceptionalTensorReassociation A a b (Ga.obj (constantComplex A Y))
            (Gb.obj (constantComplex A Z)) K ≫
          ((derivedTensor (ModuleCat.{u + 1} A) X).obj
            (Ga.obj (constantComplex A Y))).map
              ((L(upperStar (ModuleCat.{u + 1} A) a)).map
                (sfEtaleAmbientTensorMap A cb Gb adjb K)) ≫
          sfEtaleAmbientTensorMap A ca Ga adja (Gb.obj K)) ∧
      ((∃ V : DerivedCategoryModule A Y,
        Nonempty ((((derivedTensor (ModuleCat.{u + 1} A) Y).obj
          (Gb.obj (constantComplex A Z))).obj V) ≅ constantComplex A Y) ∧
        Nonempty ((((derivedTensor (ModuleCat.{u + 1} A) Y).obj V).obj
          (Gb.obj (constantComplex A Z))) ≅ constantComplex A Y)) →
        ∀ K : DerivedCategoryModule A Z, IsIso (sfEtaleAmbientTensorMap A cb Gb adjb K) →
          IsIso (sfEtaleAmbientTensorMap A ch Gh adjh K)) := by
  let Fa := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca
  let Fb := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb
  let Fh := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch
  let TX := derivedTensor (ModuleCat.{u + 1} A) X
  let TY := derivedTensor (ModuleCat.{u + 1} A) Y
  let TZ := derivedTensor (ModuleCat.{u + 1} A) Z
  let Ua := L(upperStar (ModuleCat.{u + 1} A) a)
  let Ub := L(upperStar (ModuleCat.{u + 1} A) b)
  let Uh := L(upperStar (ModuleCat.{u + 1} A) (a ≫ b))
  let W := Ga.obj (constantComplex A Y)
  let V := Gb.obj (constantComplex A Z)
  let H := Gh.obj (constantComplex A Z)
  let M := (TX.obj W).obj (Ua.obj V)
  let E := sfGraphCompactSupportCompIso A a b ca cb ch
  let c := sfExceptionalCompComparison A a b ca cb ch Ga Gb Gh adja adjb adjh
  let δ := sfExceptionalCompDelta A a b ca cb ch Ga Gb Gh adja adjb adjh ha
  have hs := ha V
  have hδ : IsIso δ := by
    dsimp [δ, sfExceptionalCompDelta]
    infer_instance
  have hd : δ ≫ sfEtaleAmbientTensorMap A ca Ga adja V = c.hom.app (constantComplex A Z) := by
    change (c.hom.app (constantComplex A Z) ≫
      inv (sfEtaleAmbientTensorMap A ca Ga adja V)) ≫
        sfEtaleAmbientTensorMap A ca Ga adja V = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have scalar : E.inv.app H ≫ adjh.counit.app (constantComplex A Z) =
      Fb.map (Fa.map δ) ≫ Fb.map (ambientEvaluation A ca Ga adja V) ≫
        adjb.counit.app (constantComplex A Z) := by
    have h := conjugate_transpose adjh (adja.comp adjb) E
      (K := constantComplex A Z) (𝟙 (Gh.obj (constantComplex A Z)))
    simp only [Category.id_comp, Adjunction.homEquiv_counit,
      Adjunction.comp_counit_app, Functor.comp_map] at h
    change Fb.map (Fa.map (c.hom.app (constantComplex A Z))) ≫
      (Fb.map (adja.counit.app V) ≫ adjb.counit.app (constantComplex A Z)) =
        E.inv.app H ≫ Fh.map (𝟙 H) ≫ adjh.counit.app (constantComplex A Z) at h
    rw [Fh.map_id, Category.id_comp, ← hd] at h
    simp only [Fa.map_comp, Fb.map_comp, Category.assoc] at h
    rw [← Fb.map_comp_assoc (Fa.map (sfEtaleAmbientTensorMap A ca Ga adja V))] at h
    have ht := ambient_transpose A ca Ga adja V
    change Fa.map (sfEtaleAmbientTensorMap A ca Ga adja V) ≫ adja.counit.app V =
      ambientEvaluation A ca Ga adja V at ht
    rw [ht] at h
    exact h.symm
  have formula (K : DerivedCategoryModule A Z) :
      sfEtaleAmbientTensorMap A ch Gh adjh K ≫ c.hom.app K =
        (TX.map δ).app (Uh.obj K) ≫
          sfExceptionalTensorReassociation A a b W V K ≫
          (TX.obj W).map (Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K)) ≫
          sfEtaleAmbientTensorMap A ca Ga adja (Gb.obj K) := by
    let ℓ : (TZ.obj (constantComplex A Z)).obj K ⟶ K :=
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) Z K).hom
    apply ((adja.comp adjb).homEquiv _ K).symm.injective
    change ((adja.comp adjb).homEquiv _ K).symm
      (sfEtaleAmbientTensorMap A ch Gh adjh K ≫
        (conjugateIsoEquiv adjh (adja.comp adjb) E.symm).hom.app K) = _
    rw [conjugate_transpose]
    rw [Adjunction.homEquiv_counit]
    have ht := ambient_transpose A ch Gh adjh K
    change Fh.map (sfEtaleAmbientTensorMap A ch Gh adjh K) ≫ adjh.counit.app K =
      ambientEvaluation A ch Gh adjh K at ht
    rw [ht]
    have hn := ambient_naturality A ca Ga adja
      (sfEtaleAmbientTensorMap A cb Gb adjb K)
    change (TX.obj W).map (Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K)) ≫
      sfEtaleAmbientTensorMap A ca Ga adja (Gb.obj K) =
        sfEtaleAmbientTensorMap A ca Ga adja ((TY.obj V).obj (Ub.obj K)) ≫
          Ga.map (sfEtaleAmbientTensorMap A cb Gb adjb K) at hn
    rw [hn, ← Category.assoc, ← Category.assoc]
    rw [composite_transpose_post]
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      ambient_transpose]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Fb.map_comp_assoc
      (Fa.map (sfEtaleAmbientTensorMap A ca Ga adja ((TY.obj V).obj (Ub.obj K))))]
    have hta := ambient_transpose A ca Ga adja ((TY.obj V).obj (Ub.obj K))
    change Fa.map (sfEtaleAmbientTensorMap A ca Ga adja ((TY.obj V).obj (Ub.obj K))) ≫
      adja.counit.app ((TY.obj V).obj (Ub.obj K)) =
        ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K)) at hta
    rw [hta]
    -- Apply projection associativity and then composition coherence.
    change E.inv.app _ ≫ ambientEvaluation A ch Gh adjh K =
      Fb.map (Fa.map ((TX.map δ).app (Uh.obj K))) ≫
        Fb.map (Fa.map (sfExceptionalTensorReassociation A a b W V K)) ≫
        Fb.map (ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K))) ≫
        ambientEvaluation A cb Gb adjb K
    let r := (derivedTensorAssociator (ModuleCat.{u + 1} A) X W
      (Ua.obj V) (Ua.obj (Ub.obj K))).hom ≫
        (TX.obj W).map (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a V
          (Ub.obj K)).inv
    let γ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a b).hom.app K
    change _ = Fb.map (Fa.map ((TX.map δ).app (Uh.obj K))) ≫
      Fb.map (Fa.map ((TX.obj M).map γ ≫ r)) ≫
        Fb.map (ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K))) ≫
          ambientEvaluation A cb Gb adjb K
    rw [Fa.map_comp, Fb.map_comp]
    simp only [Category.assoc]
    have har := ambient_associativity_transpose A ca Ga adja V (Ub.obj K)
    change Fa.map r ≫ ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K)) =
      sfEtaleCompactProjectionInverse A ca M (Ub.obj K) ≫
        (TY.map (ambientEvaluation A ca Ga adja V)).app (Ub.obj K) at har
    have hnb := sfEtaleCompactProjectionInverse_naturality_left A cb
      (ambientEvaluation A ca Ga adja V) K
    have hp := sfEtaleCompactProjectionInverse_composition A a b ca cb ch M K
    have hnδ := sfEtaleCompactProjectionInverse_naturality_left A ch δ K
    have hscl : Fh.map δ ≫ E.hom.app M ≫
        Fb.map (ambientEvaluation A ca Ga adja V) ≫
          adjb.counit.app (constantComplex A Z) =
            adjh.counit.app (constantComplex A Z) := by
      rw [E.hom.naturality_assoc]
      change E.hom.app H ≫ Fb.map (Fa.map δ) ≫
        Fb.map (ambientEvaluation A ca Ga adja V) ≫
          adjb.counit.app (constantComplex A Z) = _
      rw [← scalar, Iso.hom_inv_id_app_assoc]
    exact projection_composition_calculation Fa Fb Fh E
      (TY.flip.obj (Ub.obj K)) (TZ.flip.obj K) δ ((TX.map δ).app (Uh.obj K))
      ((TX.obj M).map γ) r (ambientEvaluation A ca Ga adja V)
      (ambientEvaluation A ca Ga adja ((TY.obj V).obj (Ub.obj K)))
      (sfEtaleCompactProjectionInverse A ch H K)
      (sfEtaleCompactProjectionInverse A ch M K)
      (sfEtaleCompactProjectionInverse A ca M (Ub.obj K))
      (sfEtaleCompactProjectionInverse A cb (Fa.obj M) K)
      (sfEtaleCompactProjectionInverse A cb V K)
      (adjh.counit.app (constantComplex A Z))
      (adjb.counit.app (constantComplex A Z)) ℓ hscl hnδ hp har hnb
  refine ⟨hδ, formula, ?_⟩
  intro _ K hb
  have := ha (Gb.obj K)
  have : IsIso (sfEtaleAmbientTensorMap A ch Gh adjh K ≫ c.hom.app K) := by
    rw [formula]
    dsimp [sfExceptionalTensorReassociation]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (c.hom.app K)

/-- The normalized etale comparison to the left-derived model of exact pullback.
The only instance used is the normalized theorem on the selected adjunction.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
noncomputable def sfEtaleDerivedRightAdjointIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [Etale a] [IsSeparated a]
    (ca : Compactification a)
    (Ga : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adja : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca ⊣ Ga) :
    Ga ≅ L(upperStar (ModuleCat.{u + 1} A) a) :=
  letI := (sfEtaleUnitTensorArbitraryBase A a ca Ga adja).1
  asIso (sfEtaleRightAdjointComparison A a ca Ga adja) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).symm

private theorem etale_derived_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (a : X ⟶ Y) [Etale a] [IsSeparated a]
    (ca : Compactification a)
    (Ga : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adja : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca ⊣ Ga)
    (P : DerivedCategoryModule A Y) :
    sfEtaleAmbientTensorMap A ca Ga adja P ≫
        (sfEtaleDerivedRightAdjointIso A a ca Ga adja).hom.app P =
      ((derivedTensor (ModuleCat.{u + 1} A) X).map
        (sfEtaleRightAdjointUnit A a ca Ga adja)).app
          ((L(upperStar (ModuleCat.{u + 1} A) a)).obj P) ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X
          ((L(upperStar (ModuleCat.{u + 1} A) a)).obj P)).hom := by
  let TX := derivedTensor (ModuleCat.{u + 1} A) X
  let ι := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a
  have h := (sfEtaleUnitTensorArbitraryBase A a ca Ga adja).2.2.1 P
  have := (sfEtaleUnitTensorArbitraryBase A a ca Ga adja).1
  apply (cancel_epi ((TX.obj (Ga.obj (constantComplex A Y))).map (ι.inv.app P))).1
  apply (cancel_mono (ι.hom.app P)).1
  dsimp only [sfEtaleDerivedRightAdjointIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, asIso_hom]
  simp only [Category.assoc]
  change (TX.obj (Ga.obj (constantComplex A Y))).map (ι.inv.app P) ≫
      sfEtaleAmbientTensorMap A ca Ga adja P ≫
        (sfEtaleRightAdjointComparison A a ca Ga adja).app P ≫
          ι.inv.app P ≫ ι.hom.app P = _
  rw [Iso.inv_hom_id_app, Category.comp_id]
  have hn := tensor_unit_action_naturality (ModuleCat.{u + 1} A) X
    (sfEtaleRightAdjointUnit A a ca Ga adja) (ι.inv.app P)
  have hh := congrArg (fun t ↦ t ≫ ι.hom.app P) hn
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hh
  change _ = _ at hh
  rw [hh]
  exact (by simpa only [sfEtaleExactAmbientTensorMap, Category.assoc] using h)

/-- The counit-preserving restriction comparison lambda, obtained by replacing
G_a in c by normalized etale inverse image.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
noncomputable def sfExceptionalEtaleRestrictionComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ca : Compactification a) (cb : Compactification b)
    (ch : Compactification (a ≫ b))
    (Ga : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (Gb : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (Gh : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adja : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca ⊣ Ga)
    (adjb : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb ⊣ Gb)
    (adjh : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch ⊣ Gh)
    [Etale a] [IsSeparated a] :
    Gb ⋙ L(upperStar (ModuleCat.{u + 1} A) a) ≅ Gh :=
  Functor.isoWhiskerLeft Gb (sfEtaleDerivedRightAdjointIso A a ca Ga adja).symm ≪≫
    (sfExceptionalCompComparison A a b ca cb ch Ga Gb Gh adja adjb adjh).symm

/-- The equality of actual etale-restricted tensor maps under the normalized
comparison. Pullback is written on its canonically equivalent left-derived model.

Proof plan (the eight steps of the node):
1. Normalize compact support by the graph compositor. Its conjugate is c, so the
   transported counit is the composite counit (def-weil-pbc-composite-adjunction).
   Write phi_f = inverse projection followed by counit tensor identity and unitor
   (lem-sf-etale-ambient-adjoint-projection, lem-kun-tensor-unit).
2. Put M = omega_a tensor a*omega_b, s = theta_a(omega_b), d = c_A inverse s.
   The transpose of s is phi_a(omega_b). Consequently the scalar composite
   counit evaluated on d is epsilon_b followed after F_b(phi_a(omega_b)).
   Both c_A and s are invertible, proving delta is invertible.
3. Naturality of theta_a follows by transposing and counit naturality. The
   iterated tensor map has composite transpose phi_b(K) F_b(phi_a(omega_b tensor b*K)).
4. Projection associativity (lem-sf-etale-compact-projection-coherence) rewrites
   phi_a(omega_b tensor b*K) as (phi_a(omega_b) tensor identity) q_a(M,b*K).
   Naturality of q_b then combines its scalar counits.
5. Projection/compositor coherence replaces the two inverse projections by q_h.
   The scalar counit equality in step 2 identifies this with the transpose of
   c_K theta_h(K) (d tensor identity). Injectivity of the composite Hom bijection
   gives equality of the actual maps. Cancel d tensor identity to get the formula.
   Insert precisely the pullback composition, associator and tensor comparison
   of lem-kun-inverse-image-monoidal, as in sfExceptionalTensorReassociation.
6. Every factor on the right is invertible if theta_b(K) is, so theta_h(K) is.
   The tensor-invertibility hypothesis on omega_b is retained as stated, though
   it is unnecessary under the universal hypothesis on theta_a.
7. For separated etale a, let rho be the normalized comparison of
   lem-sf-etale-unit-tensor-arbitrary-base. Then lambda = rho inverse c inverse,
   and the scalar normalization identifies lambda_A inverse with the unit action
   composed with delta.
8. Apply rho to step 5. Naturality of the unitors cancels the omega_a unit;
   compose with lambda_K and lambda_A tensor identity to obtain the restriction
   equation below. No boundedness, constructibility, qc or Noetherian input occurs.

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
theorem sfExceptionalTensorEtaleRestriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (ca : Compactification a) (cb : Compactification b)
    (ch : Compactification (a ≫ b))
    (Ga : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (Gb : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A Y)
    (Gh : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A X)
    (adja : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ca ⊣ Ga)
    (adjb : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cb ⊣ Gb)
    (adjh : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) ch ⊣ Gh)
    [Etale a] [IsSeparated a] (K : DerivedCategoryModule A Z) :
    (L(upperStar (ModuleCat.{u + 1} A) a)).map
        (sfEtaleAmbientTensorMap A cb Gb adjb K) ≫
      (sfExceptionalEtaleRestrictionComparison A a b ca cb ch Ga Gb Gh adja adjb adjh).hom.app K =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a
      (Gb.obj (constantComplex A Z))
      ((L(upperStar (ModuleCat.{u + 1} A) b)).obj K)).hom ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).map
      ((sfExceptionalEtaleRestrictionComparison A a b ca cb ch Ga Gb Gh adja adjb adjh).hom.app
        (constantComplex A Z))).app
          ((L(upperStar (ModuleCat.{u + 1} A) a)).obj
            ((L(upperStar (ModuleCat.{u + 1} A) b)).obj K)) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (Gh.obj (constantComplex A Z))).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a b).inv.app K) ≫
    sfEtaleAmbientTensorMap A ch Gh adjh K := by
  let TX := derivedTensor (ModuleCat.{u + 1} A) X
  let Ua := L(upperStar (ModuleCat.{u + 1} A) a)
  let Ub := L(upperStar (ModuleCat.{u + 1} A) b)
  let Uh := L(upperStar (ModuleCat.{u + 1} A) (a ≫ b))
  let W := Ga.obj (constantComplex A Y)
  let V := Gb.obj (constantComplex A Z)
  let H := Gh.obj (constantComplex A Z)
  let η := sfEtaleRightAdjointUnit A a ca Ga adja
  let ρ := sfEtaleDerivedRightAdjointIso A a ca Ga adja
  let c := sfExceptionalCompComparison A a b ca cb ch Ga Gb Gh adja adjb adjh
  let lam := sfExceptionalEtaleRestrictionComparison A a b ca cb ch Ga Gb Gh adja adjb adjh
  have ha := (sfEtaleUnitTensorArbitraryBase A a ca Ga adja).2.2.2.2
  let δ := sfExceptionalCompDelta A a b ca cb ch Ga Gb Gh adja adjb adjh ha
  let μ := leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) a V (Ub.obj K)
  let γ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) a b).app K
  have normalize (P : DerivedCategoryModule A Y) :
      sfEtaleAmbientTensorMap A ca Ga adja P ≫ ρ.hom.app P =
        (TX.map η).app (Ua.obj P) ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X (Ua.obj P)).hom :=
    etale_derived_normalization A a ca Ga adja P
  have scalar : δ ≫ (TX.map η).app (Ua.obj V) ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X (Ua.obj V)).hom =
        lam.inv.app (constantComplex A Z) := by
    rw [← normalize, ← Category.assoc]
    have := ha V
    change ((c.hom.app (constantComplex A Z) ≫
      inv (sfEtaleAmbientTensorMap A ca Ga adja V)) ≫
        sfEtaleAmbientTensorMap A ca Ga adja V) ≫ ρ.hom.app V = _
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    dsimp only [lam, sfExceptionalEtaleRestrictionComparison, Iso.trans_inv,
      Iso.symm_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerLeft_app]
  have h := (sfExceptionalTensorTransitivity A a b ca cb ch Ga Gb Gh
    adja adjb adjh ha).2.1 K
  have hf : sfEtaleAmbientTensorMap A ch Gh adjh K ≫ lam.inv.app K =
      (TX.obj H).map γ.hom ≫
        (TX.map (lam.inv.app (constantComplex A Z))).app (Ua.obj (Ub.obj K)) ≫
          μ.inv ≫ Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K) := by
    have hh := congrArg (fun t ↦ t ≫ ρ.hom.app (Gb.obj K)) h
    simp only [Category.assoc] at hh
    change sfEtaleAmbientTensorMap A ch Gh adjh K ≫ c.hom.app K ≫
      ρ.hom.app (Gb.obj K) =
        (TX.map δ).app (Uh.obj K) ≫ sfExceptionalTensorReassociation A a b W V K ≫
          (TX.obj W).map (Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K)) ≫
            sfEtaleAmbientTensorMap A ca Ga adja (Gb.obj K) ≫ ρ.hom.app (Gb.obj K) at hh
    rw [normalize, tensor_unit_action_naturality] at hh
    change sfEtaleAmbientTensorMap A ch Gh adjh K ≫ lam.inv.app K = _ at hh
    rw [hh]
    have ht := tensor_unit_action_transport (ModuleCat.{u + 1} A) X η δ γ μ
    have hs := congrArg (fun t ↦ (TX.obj H).map γ.hom ≫
      (TX.map t).app (Ua.obj (Ub.obj K)) ≫ μ.inv ≫
        Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K)) scalar
    have ht' := congrArg (fun t ↦ t ≫
      Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K)) ht
    simp only [Category.assoc, Functor.comp_obj] at ht'
    unfold sfExceptionalTensorReassociation
    simp only [Category.assoc]
    change (TX.map δ).app (Uh.obj K) ≫
      (TX.obj ((TX.obj W).obj (Ua.obj V))).map γ.hom ≫
        (derivedTensorAssociator (ModuleCat.{u + 1} A) X W (Ua.obj V)
          (Ua.obj (Ub.obj K))).hom ≫
        (TX.obj W).map μ.inv ≫ (TX.map η).app (Ua.obj (((derivedTensor
          (ModuleCat.{u + 1} A) Y).obj V).obj (Ub.obj K))) ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) X
          (Ua.obj (((derivedTensor (ModuleCat.{u + 1} A) Y).obj V).obj
            (Ub.obj K)))).hom ≫ Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K) = _
    exact ht'.trans hs
  apply (cancel_mono (lam.inv.app K)).1
  change (Ua.map (sfEtaleAmbientTensorMap A cb Gb adjb K) ≫ lam.hom.app K) ≫
      lam.inv.app K =
    (μ.hom ≫ (TX.map (lam.hom.app (constantComplex A Z))).app (Ua.obj (Ub.obj K)) ≫
      (TX.obj H).map γ.inv ≫ sfEtaleAmbientTensorMap A ch Gh adjh K) ≫ lam.inv.app K
  simp only [Category.assoc, Iso.hom_inv_id_app]
  rw [hf]
  rw [← (TX.obj H).map_comp_assoc, γ.inv_hom_id]
  dsimp only [Functor.comp_obj]
  rw [(TX.obj H).map_id, Category.id_comp]
  rw [← NatTrans.comp_app_assoc, ← TX.map_comp, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [TX.map_id]
  simp only [NatTrans.id_app, Category.id_comp, μ.hom_inv_id_assoc]
  exact Category.comp_id _

end AlgebraicGeometry.Etale
