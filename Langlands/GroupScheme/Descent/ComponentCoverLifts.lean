import Langlands.GroupScheme.Descent.ComponentHoms
import Langlands.GroupScheme.Descent.Data

/-! # Descent coherence from unique lifts on finite overlap components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent

variable {B S T U : Scheme.{u}} {C H : GroupScheme S} {π : C ⟶ H}

/-- Unique lifts are required on this specified test scheme only. -/
def HasUniquePullbackIsoLiftsOn (π : C ⟶ H) (T : Scheme.{u}) : Prop :=
  ∀ (f g : T ⟶ S) (e : (baseChange f).obj H ≅ (baseChange g).obj H),
    ∃! a : (baseChange f).obj C ⟶ (baseChange g).obj C,
      a ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom

namespace HasUniquePullbackIsoLiftsOn

variable (hT : HasUniquePullbackIsoLiftsOn π T)

/-- The unique lift on the specified scheme. -/
def lift (f g : T ⟶ S) (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    (baseChange f).obj C ⟶ (baseChange g).obj C :=
  (hT f g e).choose

@[reassoc]
theorem lift_fac (f g : T ⟶ S) (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    hT.lift f g e ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom :=
  (hT f g e).choose_spec.1

theorem lift_unique (f g : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H)
    (a : (baseChange f).obj C ⟶ (baseChange g).obj C)
    (ha : a ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom) :
    a = hT.lift f g e :=
  (hT f g e).choose_spec.2 a ha

@[simp]
theorem lift_refl (f : T ⟶ S) :
    hT.lift f f (Iso.refl _) = 𝟙 _ :=
  (hT.lift_unique f f (Iso.refl _) (𝟙 _) (by simp)).symm

theorem lift_trans (f g h : T ⟶ S)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H)
    (d : (baseChange g).obj H ≅ (baseChange h).obj H) :
    hT.lift f h (e ≪≫ d) = hT.lift f g e ≫ hT.lift g h d := by
  symm
  apply hT.lift_unique f h (e ≪≫ d)
  simp only [Category.assoc, lift_fac, lift_fac_assoc, Iso.trans_hom]

/-- The lift is an actual isomorphism, by uniqueness on this same scheme. -/
def liftIso (f g : T ⟶ S) (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    (baseChange f).obj C ≅ (baseChange g).obj C where
  hom := hT.lift f g e
  inv := hT.lift g f e.symm
  hom_inv_id := by rw [← lift_trans]; simp
  inv_hom_id := by rw [← lift_trans]; simp

/-- Pullback compatibility only needs unique lifts on the two specified schemes. -/
theorem pullIso_liftIso (hU : HasUniquePullbackIsoLiftsOn π U)
    (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H) :
    pullIso q hf hg (hT.liftIso f g e) =
      hU.liftIso r s (pullIso q hf hg e) := by
  apply Iso.ext
  apply hU.lift_unique r s (pullIso q hf hg e)
  have h := congrArg (pullHom q hf hg) (hT.lift_fac f g e)
  simpa only [pullHom_comp q hf hg hg, pullHom_comp q hf hf hg,
    pullHom_map, pullIso_hom, liftIso] using h

variable {I : Type} [Finite I] {Z : I → Scheme.{u}}

/-- Unique lifting on each actual component implies unique lifting on their base. -/
theorem of_components (q : ∀ i, Z i ⟶ T) [IsIso (Limits.Sigma.desc q)]
    (hZ : ∀ i, HasUniquePullbackIsoLiftsOn π (Z i)) :
    HasUniquePullbackIsoLiftsOn π T := by
  intro f g e
  let a : (baseChange f).obj C ⟶ (baseChange g).obj C :=
    FiniteComponents.groupHom q (fun i =>
      (pullbackComparison f (q i) (q i ≫ f) rfl C).hom ≫
        (hZ i).lift (q i ≫ f) (q i ≫ g) (pullIso (q i) rfl rfl e) ≫
        (pullbackComparison g (q i) (q i ≫ g) rfl C).inv)
  have ha (i : I) :
      pullHom (q i) rfl rfl a =
        (hZ i).lift (q i ≫ f) (q i ≫ g) (pullIso (q i) rfl rfl e) := by
    simp [pullHom, a]
  refine ⟨a, ?_, ?_⟩
  · apply FiniteComponents.groupHom_ext q
    intro i
    apply (cancel_epi (pullbackComparison f (q i) (q i ≫ f) rfl C).inv).mp
    apply (cancel_mono (pullbackComparison g (q i) (q i ≫ g) rfl H).hom).mp
    change pullHom (q i) rfl rfl (a ≫ (baseChange g).map π) =
      pullHom (q i) rfl rfl ((baseChange f).map π ≫ e.hom)
    rw [pullHom_comp (q i) rfl rfl rfl, pullHom_comp (q i) rfl rfl rfl,
      pullHom_map, pullHom_map, ha, lift_fac, pullIso_hom]
  · intro b hb
    apply FiniteComponents.groupHom_ext q
    intro i
    apply (cancel_epi (pullbackComparison f (q i) (q i ≫ f) rfl C).inv).mp
    apply (cancel_mono (pullbackComparison g (q i) (q i ≫ g) rfl C).hom).mp
    change pullHom (q i) rfl rfl b = pullHom (q i) rfl rfl a
    rw [ha]
    apply (hZ i).lift_unique (q i ≫ f) (q i ≫ g) (pullIso (q i) rfl rfl e)
    have h := congrArg (pullHom (q i) rfl rfl) hb
    simpa only [pullHom_comp (q i) rfl rfl rfl, pullHom_map, pullIso_hom] using h

end HasUniquePullbackIsoLiftsOn

variable {p : S ⟶ B}

/-- Construct descent using lifts on the double and triple overlaps only. -/
def Datum.liftOnOverlaps (D : Datum p H)
    (h₂ : HasUniquePullbackIsoLiftsOn π (Overlap p))
    (h₃ : HasUniquePullbackIsoLiftsOn π (Triple p)) : Datum p C where
  overlap := h₂.liftIso (fst p) (snd p) D.overlap
  cocycle := by
    change
      (pullIso (p12 p) rfl rfl (h₂.liftIso (fst p) (snd p) D.overlap)).hom ≫
        (pullIso (p23 p) (p23_fst p) rfl
          (h₂.liftIso (fst p) (snd p) D.overlap)).hom =
        (pullIso (p13 p) (p13_fst p) (p13_snd p)
          (h₂.liftIso (fst p) (snd p) D.overlap)).hom
    rw [h₂.pullIso_liftIso h₃, h₂.pullIso_liftIso h₃, h₂.pullIso_liftIso h₃]
    change h₃.lift (p1 p) (p2 p) (iso12 D.overlap) ≫
        h₃.lift (p2 p) (p3 p) (iso23 D.overlap) =
      h₃.lift (p1 p) (p3 p) (iso13 D.overlap)
    rw [← h₃.lift_trans]
    have hc : iso12 D.overlap ≪≫ iso23 D.overlap = iso13 D.overlap :=
      Iso.ext D.cocycle
    rw [hc]

theorem Datum.compatible_liftOnOverlaps (D : Datum p H)
    (h₂ : HasUniquePullbackIsoLiftsOn π (Overlap p))
    (h₃ : HasUniquePullbackIsoLiftsOn π (Triple p)) :
    Compatible (D.liftOnOverlaps h₂ h₃) D π :=
  (h₂.lift_fac (fst p) (snd p) D.overlap).symm

/-- The compatible source datum is determined already on the double overlap. -/
theorem Datum.liftOnOverlaps_unique (D : Datum p H)
    (h₂ : HasUniquePullbackIsoLiftsOn π (Overlap p))
    (h₃ : HasUniquePullbackIsoLiftsOn π (Triple p))
    (E : Datum p C) (hE : Compatible E D π) : E = D.liftOnOverlaps h₂ h₃ := by
  apply Datum.ext
  apply Iso.ext
  exact h₂.lift_unique (fst p) (snd p) D.overlap E.overlap.hom hE.symm

/-- Finite decompositions reduce descent coherence to unique lifting on components. -/
def Datum.liftOnComponents (D : Datum p H)
    {I J : Type} [Finite I] [Finite J]
    {Z : I → Scheme.{u}} {W : J → Scheme.{u}}
    (q : ∀ i, Z i ⟶ Overlap p) (r : ∀ j, W j ⟶ Triple p)
    [IsIso (Limits.Sigma.desc q)] [IsIso (Limits.Sigma.desc r)]
    (hZ : ∀ i, HasUniquePullbackIsoLiftsOn π (Z i))
    (hW : ∀ j, HasUniquePullbackIsoLiftsOn π (W j)) : Datum p C :=
  D.liftOnOverlaps (.of_components q hZ) (.of_components r hW)

theorem Datum.compatible_liftOnComponents (D : Datum p H)
    {I J : Type} [Finite I] [Finite J]
    {Z : I → Scheme.{u}} {W : J → Scheme.{u}}
    (q : ∀ i, Z i ⟶ Overlap p) (r : ∀ j, W j ⟶ Triple p)
    [IsIso (Limits.Sigma.desc q)] [IsIso (Limits.Sigma.desc r)]
    (hZ : ∀ i, HasUniquePullbackIsoLiftsOn π (Z i))
    (hW : ∀ j, HasUniquePullbackIsoLiftsOn π (W j)) :
    Compatible (D.liftOnComponents q r hZ hW) D π :=
  D.compatible_liftOnOverlaps _ _

/-- Uniqueness for one specified pair of endpoints and one target isomorphism. -/
def PullbackIsoLiftUnique {f g : T ⟶ S}
    (π : C ⟶ H) (e : (baseChange f).obj H ≅ (baseChange g).obj H) : Prop :=
  ∀ (a b : (baseChange f).obj C ⟶ (baseChange g).obj C),
    a ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom →
    b ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom → a = b

/-- A lifting equation remains a lifting equation under actual further pullback. -/
theorem pullHom_lift_fac (q : U ⟶ T) {f g : T ⟶ S} {r s : U ⟶ S}
    (hf : q ≫ f = r) (hg : q ≫ g = s)
    (e : (baseChange f).obj H ≅ (baseChange g).obj H)
    (a : (baseChange f).obj C ⟶ (baseChange g).obj C)
    (ha : a ≫ (baseChange g).map π = (baseChange f).map π ≫ e.hom) :
    pullHom q hf hg a ≫ (baseChange s).map π =
      (baseChange r).map π ≫ (pullIso q hf hg e).hom := by
  have h := congrArg (pullHom q hf hg) ha
  simpa only [pullHom_comp q hf hg hg, pullHom_comp q hf hf hg,
    pullHom_map, pullIso_hom] using h

namespace FiniteComponents

variable {I : Type} [Finite I] {Z : I → Scheme.{u}}
variable (q : ∀ i, Z i ⟶ T) [IsIso (Limits.Sigma.desc q)]

/-- Conjugated component restrictions jointly detect equality of pullback maps. -/
theorem pullHom_ext {f g : T ⟶ S}
    {a b : (baseChange f).obj C ⟶ (baseChange g).obj H}
    (h : ∀ i, pullHom (q i) rfl rfl a = pullHom (q i) rfl rfl b) : a = b := by
  apply groupHom_ext q
  intro i
  apply (cancel_epi (pullbackComparison f (q i) (q i ≫ f) rfl C).inv).mp
  apply (cancel_mono (pullbackComparison g (q i) (q i ≫ g) rfl H).hom).mp
  exact h i

/-- Assemble isomorphisms whose endpoints are direct pullbacks from the original base. -/
def pullbackIso {f g : T ⟶ S}
    (a : ∀ i, (baseChange (q i ≫ f)).obj C ≅ (baseChange (q i ≫ g)).obj C) :
    (baseChange f).obj C ≅ (baseChange g).obj C :=
  groupIso q (fun i =>
    pullbackComparison f (q i) (q i ≫ f) rfl C ≪≫ a i ≪≫
      (pullbackComparison g (q i) (q i ≫ g) rfl C).symm)

@[simp]
theorem pullIso_pullbackIso {f g : T ⟶ S}
    (a : ∀ i, (baseChange (q i ≫ f)).obj C ≅ (baseChange (q i ≫ g)).obj C)
    (i : I) :
    pullIso (q i) rfl rfl (pullbackIso q a) = a i := by
  simp [pullIso, pullbackIso]

/-- Assemble the component lifting equations for these specified endpoints. -/
theorem pullbackIso_fac {f g : T ⟶ S}
    (e : (baseChange f).obj H ≅ (baseChange g).obj H)
    (a : ∀ i, (baseChange (q i ≫ f)).obj C ≅ (baseChange (q i ≫ g)).obj C)
    (ha : ∀ i, (a i).hom ≫ (baseChange (q i ≫ g)).map π =
      (baseChange (q i ≫ f)).map π ≫ (pullIso (q i) rfl rfl e).hom) :
    (pullbackIso q a).hom ≫ (baseChange g).map π =
      (baseChange f).map π ≫ e.hom := by
  apply pullHom_ext q
  intro i
  rw [pullHom_comp (q i) rfl rfl rfl, pullHom_comp (q i) rfl rfl rfl,
    pullHom_map, pullHom_map]
  change (pullIso (q i) rfl rfl (pullbackIso q a)).hom ≫ _ = _
  simpa only [pullIso_pullbackIso, pullIso_hom] using ha i

end FiniteComponents

/-- Uniqueness only for the actual first-to-third transport on triple components
forces the source cocycle. -/
theorem cocycle_of_component_lift_unique (D : Datum p H) (e : OverlapIso p C)
    (he : e.hom ≫ (baseChange (snd p)).map π =
      (baseChange (fst p)).map π ≫ D.overlap.hom)
    {J : Type} [Finite J] {W : J → Scheme.{u}}
    (r : ∀ j, W j ⟶ Triple p) [IsIso (Limits.Sigma.desc r)]
    (hW : ∀ j, PullbackIsoLiftUnique π (pullIso (r j) rfl rfl (iso13 D.overlap))) :
    Cocycle e := by
  have h12 := pullHom_lift_fac (p12 p) rfl rfl D.overlap e.hom he
  have h23 := pullHom_lift_fac (p23 p) (p23_fst p) rfl D.overlap e.hom he
  have h13 := pullHom_lift_fac (p13 p) (p13_fst p) (p13_snd p) D.overlap e.hom he
  change (iso12 e).hom ≫ (baseChange (p2 p)).map π =
    (baseChange (p1 p)).map π ≫ (iso12 D.overlap).hom at h12
  change (iso23 e).hom ≫ (baseChange (p3 p)).map π =
    (baseChange (p2 p)).map π ≫ (iso23 D.overlap).hom at h23
  change (iso13 e).hom ≫ (baseChange (p3 p)).map π =
    (baseChange (p1 p)).map π ≫ (iso13 D.overlap).hom at h13
  have hc : ((iso12 e).hom ≫ (iso23 e).hom) ≫ (baseChange (p3 p)).map π =
      (baseChange (p1 p)).map π ≫ (iso13 D.overlap).hom := by
    rw [Category.assoc, h23, ← Category.assoc, h12, Category.assoc, D.cocycle]
  apply FiniteComponents.pullHom_ext r
  intro j
  exact hW j _ _
    (pullHom_lift_fac (r j) rfl rfl (iso13 D.overlap) _ hc)
    (pullHom_lift_fac (r j) rfl rfl (iso13 D.overlap) _ h13)

/-- Construct a source datum using only the specified component isomorphisms and
uniqueness for the specified first-to-third triple transport. -/
def Datum.liftFromComponentIsos (D : Datum p H)
    {I J : Type} [Finite I] [Finite J]
    {Z : I → Scheme.{u}} {W : J → Scheme.{u}}
    (q : ∀ i, Z i ⟶ Overlap p) (r : ∀ j, W j ⟶ Triple p)
    [IsIso (Limits.Sigma.desc q)] [IsIso (Limits.Sigma.desc r)]
    (a : ∀ i, (baseChange (q i ≫ fst p)).obj C ≅
      (baseChange (q i ≫ snd p)).obj C)
    (ha : ∀ i, (a i).hom ≫ (baseChange (q i ≫ snd p)).map π =
      (baseChange (q i ≫ fst p)).map π ≫ (pullIso (q i) rfl rfl D.overlap).hom)
    (hW : ∀ j, PullbackIsoLiftUnique π (pullIso (r j) rfl rfl (iso13 D.overlap))) :
    Datum p C where
  overlap := FiniteComponents.pullbackIso q a
  cocycle := cocycle_of_component_lift_unique D _ (FiniteComponents.pullbackIso_fac q
    D.overlap a ha) r hW

theorem Datum.compatible_liftFromComponentIsos (D : Datum p H)
    {I J : Type} [Finite I] [Finite J]
    {Z : I → Scheme.{u}} {W : J → Scheme.{u}}
    (q : ∀ i, Z i ⟶ Overlap p) (r : ∀ j, W j ⟶ Triple p)
    [IsIso (Limits.Sigma.desc q)] [IsIso (Limits.Sigma.desc r)]
    (a : ∀ i, (baseChange (q i ≫ fst p)).obj C ≅
      (baseChange (q i ≫ snd p)).obj C)
    (ha : ∀ i, (a i).hom ≫ (baseChange (q i ≫ snd p)).map π =
      (baseChange (q i ≫ fst p)).map π ≫ (pullIso (q i) rfl rfl D.overlap).hom)
    (hW : ∀ j, PullbackIsoLiftUnique π (pullIso (r j) rfl rfl (iso13 D.overlap))) :
    Compatible (D.liftFromComponentIsos q r a ha hW) D π :=
  (FiniteComponents.pullbackIso_fac q D.overlap a ha).symm

end Langlands.GroupScheme.Descent
