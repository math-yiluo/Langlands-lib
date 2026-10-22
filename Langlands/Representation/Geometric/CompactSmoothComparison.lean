import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Geometric.SmoothSupportFiltration
import Langlands.Representation.Filtration.IsoTransport
import Mathlib.CategoryTheory.Whiskering

/-! Canonical compact-to-smooth comparison and transport of the actual support quotients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace Langlands

universe uR uG uV uC vC

namespace RepSubfunctor

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {C : Type uC} [Category.{vC} C] {F F' : C ⥤ Rep.{uV} R G}
  (S T : RepSubfunctor F) (S' T' : RepSubfunctor F')

/-- An actual natural isomorphism of upper subfunctors descends when it identifies
exactly their pulled-back lower submodules. -/
def quotientNatIso (e : T.toFunctor ≅ T'.toFunctor)
    (h : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X ↔ (e.hom.app X).hom v ∈ S'.lowerInUpper T' X) :
    S.quotientFunctor T ≅ S'.quotientFunctor T' where
  hom := quotientNatMap S T S' T' e.hom (fun X v => (h X v).mp)
  inv := quotientNatMap S' T' S T e.inv (by
    intro X v hv
    apply (h X ((e.inv.app X).hom v)).mpr
    have he := Rep.hom_inv_apply _ _ (e.app X) v
    change (e.hom.app X).hom ((e.inv.app X).hom v) = v at he
    rw [he]
    exact hv)
  hom_inv_id := by
    apply NatTrans.ext
    funext X
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := S.quotientProjection_surjective T X v
    change (S.quotientProjection T X).hom ((e.inv.app X).hom ((e.hom.app X).hom v)) =
      (S.quotientProjection T X).hom v
    congr 1
    exact Rep.inv_hom_apply _ _ (e.app X) v
  inv_hom_id := by
    apply NatTrans.ext
    funext X
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := S'.quotientProjection_surjective T' X v
    change (S'.quotientProjection T' X).hom ((e.hom.app X).hom ((e.inv.app X).hom v)) =
      (S'.quotientProjection T' X).hom v
    congr 1
    exact Rep.hom_inv_apply _ _ (e.app X) v

@[simp]
theorem quotientNatIso_hom_projection (e : T.toFunctor ≅ T'.toFunctor)
    (h : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X ↔ (e.hom.app X).hom v ∈ S'.lowerInUpper T' X)
    (X : C) (v : T.representation X) :
    ((quotientNatIso S T S' T' e h).hom.app X).hom
        ((S.quotientProjection T X).hom v) =
      (S'.quotientProjection T' X).hom ((e.hom.app X).hom v) := rfl

@[simp]
theorem quotientNatIso_inv_projection (e : T.toFunctor ≅ T'.toFunctor)
    (h : ∀ (X : C) (v : T.representation X),
      v ∈ S.lowerInUpper T X ↔ (e.hom.app X).hom v ∈ S'.lowerInUpper T' X)
    (X : C) (v : T'.representation X) :
    ((quotientNatIso S T S' T' e h).inv.app X).hom
        ((S'.quotientProjection T' X).hom v) =
      (S.quotientProjection T X).hom ((e.inv.app X).hom v) := rfl

end RepSubfunctor

namespace Induction

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical inclusion as a natural transformation of the actual induction functors. -/
def compactSmoothInclusion (P : Subgroup G) :
    compactInductionFunctor.{uR, uG, uV} (R := R) P ⟶ smoothInductionFunctor P where
  app A := SmoothRep.ofHom (compactInclusion P A.ρ)
  naturality _ _ _ := rfl

/-- Compact quotient makes the canonical natural inclusion an isomorphism. -/
def compactSmoothIso (P : Subgroup G) [CompactSpace (LeftQuotient P)] :
    compactInductionFunctor.{uR, uG, uV} (R := R) P ≅ smoothInductionFunctor P :=
  NatIso.ofComponents
    (fun A => SmoothRep.mkIso ((compactInclusion P A.ρ).ofBijective
      (compactInclusion_bijective_of_compactSpace P A.ρ)))
    (fun _ => rfl)

@[simp]
theorem compactSmoothIso_hom (P : Subgroup G) [CompactSpace (LeftQuotient P)] :
    (compactSmoothIso.{uR, uG, uV} (R := R) P).hom = compactSmoothInclusion P := rfl

@[simp]
theorem compactSmoothIso_hom_app (P : Subgroup G) [CompactSpace (LeftQuotient P)]
    (A : Rep.{uV} R P) :
    SmoothRep.hom ((compactSmoothIso P).hom.app A) = compactInclusion P A.ρ := rfl

@[simp]
theorem compactSmoothIso_inv_apply_val (P : Subgroup G) [CompactSpace (LeftQuotient P)]
    (A : Rep.{uV} R P) (f : SmoothFunctions P A.ρ) :
    (SmoothRep.hom ((compactSmoothIso P).inv.app A) f).val = f :=
  ((compactInclusion P A.ρ).ofBijective
    (compactInclusion_bijective_of_compactSpace P A.ρ)).apply_symm_apply f

end Induction

namespace Geometric

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restrict the canonical compact-to-smooth isomorphism to Q. -/
def rawRestrictedCompactSmoothIso (P Q : Subgroup G)
    [CompactSpace (Induction.LeftQuotient P)] :
    rawRestrictedCompactInduction.{uR, uG, uV} (R := R) P Q ≅
      rawRestrictedSmoothInduction P Q :=
  Functor.isoWhiskerRight (Induction.compactSmoothIso P)
    (SmoothRep.toRep ⋙ Rep.resFunctor Q.subtype)

/-- On each actual support space the forward map keeps the same smooth function. -/
def rawSupportCompactSmoothMap (P Q : Subgroup G) (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U) :
    (rawSupportSubfunctor.{uR, uG, uV} (R := R) P Q U hU).toFunctor ⟶
      (rawSmoothSupportSubfunctor P Q U hU).toFunctor where
  app _A := Rep.ofHom
    { toLinearMap :=
        { toFun := fun f => ⟨f.val.val, f.property⟩
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      isIntertwining' _ := rfl }
  naturality _ _ _ := rfl

/-- The comparison is a natural isomorphism on every invariant support set. -/
def rawSupportCompactSmoothIso (P Q : Subgroup G) (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U)
    [CompactSpace (Induction.LeftQuotient P)] :
    (rawSupportSubfunctor.{uR, uG, uV} (R := R) P Q U hU).toFunctor ≅
      (rawSmoothSupportSubfunctor P Q U hU).toFunctor :=
  NatIso.ofComponents (fun A => Rep.mkIso
    (((rawSupportCompactSmoothMap P Q U hU).app A).hom.ofBijective (by
      constructor
      · intro f g h
        apply Subtype.ext
        apply Subtype.ext
        change (⟨f.val.val, f.property⟩ :
          (rawSmoothSupportSubfunctor P Q U hU).representation A) =
          ⟨g.val.val, g.property⟩ at h
        exact congrArg (fun k : (rawSmoothSupportSubfunctor P Q U hU).representation A => k.val) h
      · intro f
        obtain ⟨g, hg⟩ := (Induction.compactInclusion_bijective_of_compactSpace P A.ρ).surjective f.val
        refine ⟨⟨g, ?_⟩, ?_⟩
        · change ∀ x, Induction.eval P A.ρ g.val x ≠ 0 → Induction.quotientMap P x ∈ U
          change g.val = f.val at hg
          rw [hg]
          exact f.property
        · apply Subtype.ext
          exact hg))) (fun _ => rfl)

@[simp]
theorem rawSupportCompactSmoothIso_hom (P Q : Subgroup G)
    (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U)
    [CompactSpace (Induction.LeftQuotient P)] :
    (rawSupportCompactSmoothIso.{uR, uG, uV} (R := R) P Q U hU).hom =
      rawSupportCompactSmoothMap P Q U hU := rfl

@[simp]
theorem rawRestrictedCompactSmoothIso_hom_apply (P Q : Subgroup G)
    [CompactSpace (Induction.LeftQuotient P)] (A : Rep.{uV} R P)
    (f : Induction.CompactFunctions P A.ρ) :
    ((rawRestrictedCompactSmoothIso P Q).hom.app A).hom f = f.val := rfl

@[simp]
theorem rawSupportCompactSmoothIso_hom_apply_val (P Q : Subgroup G)
    (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U)
    [CompactSpace (Induction.LeftQuotient P)] (A : Rep.{uV} R P)
    (f : (rawSupportSubfunctor (R := R) P Q U hU).representation A) :
    (((rawSupportCompactSmoothIso P Q U hU).hom.app A).hom f).val = f.val.val := rfl

/-- The support comparison commutes with the canonical inclusions. -/
theorem rawSupportCompactSmoothIso_inclusion (P Q : Subgroup G)
    (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U)
    [CompactSpace (Induction.LeftQuotient P)] :
    (rawSupportCompactSmoothIso.{uR, uG, uV} (R := R) P Q U hU).hom ≫
        (rawSmoothSupportSubfunctor P Q U hU).inclusion =
      (rawSupportSubfunctor P Q U hU).inclusion ≫
        (rawRestrictedCompactSmoothIso P Q).hom := rfl

@[simp]
theorem rawSupportCompactSmoothIso_inv_apply_val (P Q : Subgroup G)
    (U : Set (Induction.LeftQuotient P))
    (hU : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ U →
      Induction.quotientRight P (q : G) x ∈ U)
    [CompactSpace (Induction.LeftQuotient P)] (A : Rep.{uV} R P)
    (f : (rawSmoothSupportSubfunctor (R := R) P Q U hU).representation A) :
    (((rawSupportCompactSmoothIso P Q U hU).inv.app A).hom f).val.val = f.val := by
  exact congrArg (fun k : (rawSmoothSupportSubfunctor P Q U hU).representation A => k.val)
    (Rep.hom_inv_apply _ _ ((rawSupportCompactSmoothIso P Q U hU).app A) f)

namespace OrderedDoubleCosets

variable {P Q : Subgroup G} {n : ℕ} [CompactSpace (Induction.LeftQuotient P)]

/-- Compare the same step of the two specified support filtrations. -/
def rawSupportStepCompactSmoothIso (s : OrderedDoubleCosets P Q n) (k : Fin (n + 1)) :
    ((rawSupportFiltration.{uR, uG, uV} (R := R) s).step k).toFunctor ≅
      ((s.rawSmoothSupportFiltration (R := R)).step k).toFunctor :=
  rawSupportCompactSmoothIso P Q (s.initialOrbits k)
    (fun q _ hx => s.initialOrbits_right_invariant k q hx)

/-- Every step inclusion commutes with the same ambient comparison. -/
theorem rawSupportStepCompactSmoothIso_inclusion
    (s : OrderedDoubleCosets P Q n) (k : Fin (n + 1)) :
    (rawSupportStepCompactSmoothIso.{uR, uG, uV} (R := R) s k).hom ≫
        ((s.rawSmoothSupportFiltration (R := R)).step k).inclusion =
      ((s.rawSupportFiltration (R := R)).step k).inclusion ≫
        (rawRestrictedCompactSmoothIso P Q).hom := rfl

/-- Compare the actual successive quotients, retaining both the index and orbit order. -/
def rawSupportGradedCompactSmoothIso (s : OrderedDoubleCosets P Q n) (i : Fin n) :
    (rawSupportFiltration.{uR, uG, uV} (R := R) s).graded i ≅
      (s.rawSmoothSupportFiltration (R := R)).graded i :=
  RepSubfunctor.quotientNatIso
    ((s.rawSupportFiltration (R := R)).step i.castSucc)
    ((s.rawSupportFiltration (R := R)).step i.succ)
    ((s.rawSmoothSupportFiltration (R := R)).step i.castSucc)
    ((s.rawSmoothSupportFiltration (R := R)).step i.succ)
    (s.rawSupportStepCompactSmoothIso i.succ) (fun _ _ => Iff.rfl)

/-- The forward graded comparison sends the class of f to the class of the same function. -/
@[simp]
theorem rawSupportGradedCompactSmoothIso_hom_projection
    (s : OrderedDoubleCosets P Q n) (i : Fin n) (A : Rep.{uV} R P)
    (f : ((s.rawSupportFiltration (R := R)).step i.succ).representation A) :
    ((s.rawSupportGradedCompactSmoothIso i).hom.app A).hom
        ((((s.rawSupportFiltration (R := R)).step i.castSucc).quotientProjection
          ((s.rawSupportFiltration (R := R)).step i.succ) A).hom f) =
      (((s.rawSmoothSupportFiltration (R := R)).step i.castSucc).quotientProjection
        ((s.rawSmoothSupportFiltration (R := R)).step i.succ) A).hom
        (((s.rawSupportStepCompactSmoothIso i.succ).hom.app A).hom f) := rfl

/-- The canonical projections commute as natural transformations. -/
theorem rawSupportGradedCompactSmoothIso_projection
    (s : OrderedDoubleCosets P Q n) (i : Fin n) :
    ((rawSupportFiltration.{uR, uG, uV} (R := R) s).step i.castSucc).quotientNatProjection
        ((s.rawSupportFiltration (R := R)).step i.succ) ≫
        (s.rawSupportGradedCompactSmoothIso i).hom =
      (s.rawSupportStepCompactSmoothIso i.succ).hom ≫
        ((s.rawSmoothSupportFiltration (R := R)).step i.castSucc).quotientNatProjection
          ((s.rawSmoothSupportFiltration (R := R)).step i.succ) := rfl

end OrderedDoubleCosets
end Geometric
end Langlands
