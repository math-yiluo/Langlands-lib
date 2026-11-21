import Langlands.Geometry.Analytic.LocalizedSigmaNearness
import Langlands.Geometry.Analytic.LocalizedDisjointUnion
import Langlands.Geometry.Analytic.NearIdentityDomainRestriction
import Langlands.Geometry.Analytic.OpenPartitionCoproduct
import Mathlib.Topology.LocallyConstant.Basic

/-! # Morphisms over `X` into a disjoint union of copies of `X` -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ## Points of disjoint unions -/

section Points

variable {J : Type z} (Xf : J → LocalizedCategory.{u, max z v, max z v} (K := K))

/-- A morphism out of a disjoint union, at a point of a summand. -/
theorem sigma_map_apply {Y : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (m : (localizedSigmaCofan Xf).pt ⟶ Y) (j : J) (x : localizedSpaceFunctor.obj (Xf j)) :
    localizedSpaceFunctor.map m
        (⟨j, x⟩ : (i : J) × (presentationOf (Xf i)).presentation.space) =
      localizedSpaceFunctor.map ((localizedSigmaCofan Xf).inj j ≫ m) x := by
  rw [Functor.map_comp, ← localizedSpaceFunctor_map_localizedSigmaCofan_inj Xf j x]
  rfl

/-- The index of the summand containing the image of a point. -/
def index {U : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (φ : U ⟶ (localizedSigmaCofan Xf).pt) (x : localizedSpaceFunctor.obj U) : J :=
  (localizedSpaceFunctor.map φ x).1

theorem isLocallyConstant_index {U : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (φ : U ⟶ (localizedSigmaCofan Xf).pt) : IsLocallyConstant (index Xf φ) := by
  have h : IsLocallyConstant
      (Sigma.fst : ((i : J) × (presentationOf (Xf i)).presentation.space) → J) :=
    IsLocallyConstant.iff_isOpen_fiber.2 fun j => by
      rw [← Set.range_sigmaMk]
      exact isOpen_range_sigmaMk
  exact h.comp_continuous (localizedSpaceFunctor.map φ).hom.continuous

theorem index_comp {U V : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (a : U ⟶ V) (φ : V ⟶ (localizedSigmaCofan Xf).pt) (x : localizedSpaceFunctor.obj U) :
    index Xf (a ≫ φ) x = index Xf φ (localizedSpaceFunctor.map a x) := by
  unfold index
  rw [Functor.map_comp]
  rfl

theorem index_comp_inj {U : LocalizedCategory.{u, max z v, max z v} (K := K)} (j : J)
    (a : U ⟶ Xf j) (x : localizedSpaceFunctor.obj U) :
    index Xf (a ≫ (localizedSigmaCofan Xf).inj j) x = j := by
  rw [index_comp]
  exact congrArg Sigma.fst (localizedSpaceFunctor_map_localizedSigmaCofan_inj Xf j _)

end Points

/-! ## The open domains of the copies -/

section Copies

variable {S : Type z} (X : LocalizedCategory.{u, max z v, max z v} (K := K))

/-- The codiagonal morphism `⊔_{s ∈ S} X → X`. -/
abbrev codiag : (localizedSigmaCofan fun _ : S => X).pt ⟶ X :=
  Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : S => X) fun _ => 𝟙 X

theorem inj_codiag (s : S) : (localizedSigmaCofan fun _ : S => X).inj s ≫ codiag X = 𝟙 X :=
  Cofan.IsColimit.fac _ _ s

theorem inj_codiag_assoc (s : S) {Y : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (f : X ⟶ Y) : (localizedSigmaCofan fun _ : S => X).inj s ≫ codiag X ≫ f = f := by
  rw [← Category.assoc, inj_codiag, Category.id_comp]

/-- The points of the copy `s` of `X`, as an open subset of `⊔_{s ∈ S} X`. -/
def copySet (s : S) : Set (presentationOf (localizedSigmaCofan fun _ : S => X).pt).presentation.space :=
  (Sigma.fst ⁻¹' {s} : Set ((_ : S) × (presentationOf X).presentation.space))

theorem isOpen_copySet (s : S) : IsOpen (copySet X s) :=
  isOpen_sigma_fst_preimage (σ := fun _ : S => (presentationOf X).presentation.space) {s}

/-- The copy `s` of `X`, as an open domain of `⊔_{s ∈ S} X`. -/
abbrev copyDomain (s : S) : (presentationOf (localizedSigmaCofan fun _ : S => X).pt).AnalyticDomain :=
  (presentationOf _).openDomain (copySet X s) (isOpen_copySet X s)

theorem pairwise_disjoint_copySet :
    Pairwise fun s t : S => Disjoint (copySet X s) (copySet X t) := fun _ _ hst =>
  Set.disjoint_left.2 fun _ hs ht => hst ((Set.mem_singleton_iff.1 hs).symm.trans ht)

theorem exists_mem_copySet (y : (presentationOf (localizedSigmaCofan fun _ : S => X).pt).presentation.space) :
    ∃ s : S, y ∈ copySet X s :=
  ⟨(y : (_ : S) × (presentationOf X).presentation.space).1, rfl⟩

/-- The disjoint union is the coproduct of the open domains of the copies. -/
def isColimitCopyDomains :
    IsColimit (Cofan.mk (localizedSigmaCofan fun _ : S => X).pt fun s =>
      domainι (localizedSigmaCofan fun _ : S => X).pt (copyDomain X s)) :=
  isColimitOpenPartition _ (copySet X) (isOpen_copySet X) (pairwise_disjoint_copySet X)
    (exists_mem_copySet X)

theorem inj_mem_copySet (s : S) (x : localizedSpaceFunctor.obj X) :
    localizedSpaceFunctor.map ((localizedSigmaCofan fun _ : S => X).inj s) x ∈ copySet X s :=
  congrArg Sigma.fst (localizedSpaceFunctor_map_localizedSigmaCofan_inj (fun _ : S => X) s x)

/-- On the open domain of the copy `s`, the codiagonal followed by the inclusion of the copy `s`
is the canonical morphism of the domain. -/
theorem domainι_copyDomain_comp_codiag_inj (s : S) :
    domainι _ (copyDomain X s) ≫ codiag X ≫ (localizedSigmaCofan fun _ : S => X).inj s =
      domainι _ (copyDomain X s) := by
  set C := localizedSigmaCofan fun _ : S => X
  let Φ : C.pt ⟶ C.pt := Cofan.IsColimit.desc (isColimitCopyDomains X) fun t =>
    domainι _ (copyDomain X t) ≫ codiag X ≫ C.inj t
  have hΦ : ∀ t, domainι _ (copyDomain X t) ≫ Φ =
      domainι _ (copyDomain X t) ≫ codiag X ≫ C.inj t := fun t =>
    Cofan.IsColimit.fac (isColimitCopyDomains X) _ t
  have hΦ1 : Φ = 𝟙 C.pt := by
    refine Cofan.IsColimit.hom_ext (isColimitLocalizedSigmaCofan fun _ : S => X) _ _ fun t => ?_
    have hl := domainLift_comp (copyDomain X t) (C.inj t) (inj_mem_copySet X t)
    rw [Category.comp_id]
    calc C.inj t ≫ Φ
        = domainLift (copyDomain X t) (C.inj t) (inj_mem_copySet X t) ≫
            domainι _ (copyDomain X t) ≫ Φ := by rw [← Category.assoc, hl]
      _ = domainLift (copyDomain X t) (C.inj t) (inj_mem_copySet X t) ≫
            domainι _ (copyDomain X t) ≫ codiag X ≫ C.inj t := by rw [hΦ]
      _ = C.inj t := by rw [← Category.assoc, hl, inj_codiag_assoc]
  rw [← hΦ, hΦ1, Category.comp_id]

/-- A morphism into `⊔_{s ∈ S} X` landing in the copy `s` is recovered from its composite with
the codiagonal. -/
theorem eq_comp_codiag_inj {W : LocalizedCategory.{u, max z v, max z v} (K := K)} (s : S)
    (f : W ⟶ (localizedSigmaCofan fun _ : S => X).pt) (hf : ∀ w, index (fun _ : S => X) f w = s) :
    f = f ≫ codiag X ≫ (localizedSigmaCofan fun _ : S => X).inj s := by
  have hl := domainLift_comp (copyDomain X s) f hf
  calc f = domainLift (copyDomain X s) f hf ≫ domainι _ (copyDomain X s) := hl.symm
    _ = domainLift (copyDomain X s) f hf ≫ domainι _ (copyDomain X s) ≫ codiag X ≫
          (localizedSigmaCofan fun _ : S => X).inj s := by
      rw [domainι_copyDomain_comp_codiag_inj]
    _ = f ≫ codiag X ≫ (localizedSigmaCofan fun _ : S => X).inj s := by
      rw [← Category.assoc, hl]

end Copies

/-! ## Morphisms over `X` into the copies -/

section OverHom

variable {S : Type z} {X U : LocalizedCategory.{u, max z v, max z v} (K := K)}

/-- The fibre of a locally constant map `c : U → S` over `s`, as an open domain of `U`. -/
abbrev fibreDomain (c : localizedSpaceFunctor.obj U → S) (hc : IsLocallyConstant c) (s : S) :
    (presentationOf U).AnalyticDomain :=
  (presentationOf U).openDomain (c ⁻¹' {s}) (hc.isOpen_fiber s)

/-- The space `U` is the coproduct of the fibres of a locally constant map `c : U → S`. -/
def isColimitFibreDomains (c : localizedSpaceFunctor.obj U → S) (hc : IsLocallyConstant c) :
    IsColimit (Cofan.mk U fun s => domainι U (fibreDomain c hc s)) :=
  isColimitOpenPartition U (fun s => c ⁻¹' {s}) (fun s => hc.isOpen_fiber s)
    (fun _ _ hst => Set.disjoint_left.2 fun _ hs ht =>
      hst ((Set.mem_singleton_iff.1 hs).symm.trans ht))
    (fun y => ⟨c y, rfl⟩)

/-- The morphism `U → ⊔_{s ∈ S} X` over `p : U → X` sending the fibre of `c` over `s` into the
copy `s`. -/
def overHom (p : U ⟶ X) (c : localizedSpaceFunctor.obj U → S) (hc : IsLocallyConstant c) :
    U ⟶ (localizedSigmaCofan fun _ : S => X).pt :=
  Cofan.IsColimit.desc (isColimitFibreDomains c hc) fun s =>
    domainι U (fibreDomain c hc s) ≫ p ≫ (localizedSigmaCofan fun _ : S => X).inj s

theorem domainι_comp_overHom (p : U ⟶ X) (c : localizedSpaceFunctor.obj U → S)
    (hc : IsLocallyConstant c) (s : S) :
    domainι U (fibreDomain c hc s) ≫ overHom p c hc =
      domainι U (fibreDomain c hc s) ≫ p ≫ (localizedSigmaCofan fun _ : S => X).inj s :=
  Cofan.IsColimit.fac (isColimitFibreDomains c hc) _ s

theorem overHom_comp_codiag (p : U ⟶ X) (c : localizedSpaceFunctor.obj U → S)
    (hc : IsLocallyConstant c) : overHom p c hc ≫ codiag X = p := by
  refine Cofan.IsColimit.hom_ext (isColimitFibreDomains c hc) _ _ fun s => ?_
  change domainι U (fibreDomain c hc s) ≫ overHom p c hc ≫ codiag X =
    domainι U (fibreDomain c hc s) ≫ p
  rw [← Category.assoc, domainι_comp_overHom, Category.assoc, Category.assoc, inj_codiag,
    Category.comp_id]

theorem index_overHom (p : U ⟶ X) (c : localizedSpaceFunctor.obj U → S)
    (hc : IsLocallyConstant c) (x : localizedSpaceFunctor.obj U) :
    index (fun _ : S => X) (overHom p c hc) x = c x := by
  let w : localizedSpaceFunctor.obj (domainObj U (fibreDomain c hc (c x))) :=
    Subtype.mk (p := (· ∈ (fibreDomain c hc (c x)).carrier)) x rfl
  have hw : localizedSpaceFunctor.map (domainι U (fibreDomain c hc (c x))) w = x :=
    domainι_apply _ w
  rw [← hw, ← index_comp, domainι_comp_overHom, ← Category.assoc]
  exact index_comp_inj (fun _ : S => X) (c x) _ w

/-- A morphism `φ : U → ⊔_{s ∈ S} X` over `p` whose index map is `c` is `overHom p c`. -/
theorem eq_overHom {p : U ⟶ X} {c : localizedSpaceFunctor.obj U → S} (hc : IsLocallyConstant c)
    {φ : U ⟶ (localizedSigmaCofan fun _ : S => X).pt} (hφ : φ ≫ codiag X = p)
    (h : ∀ x, index (fun _ : S => X) φ x = c x) : φ = overHom p c hc := by
  refine Cofan.IsColimit.hom_ext (isColimitFibreDomains c hc) _ _ fun s => ?_
  change domainι U (fibreDomain c hc s) ≫ φ = domainι U (fibreDomain c hc s) ≫ overHom p c hc
  rw [domainι_comp_overHom]
  have hs : ∀ w, index (fun _ : S => X) (domainι U (fibreDomain c hc s) ≫ φ) w = s := fun w => by
    rw [index_comp, domainι_apply]
    exact (h _).trans w.2
  rw [eq_comp_codiag_inj X s _ hs, Category.assoc, reassoc_of% hφ]

/-- Morphisms over `p : U → X` into `⊔_{s ∈ S} X` are determined by their index maps. -/
theorem copiesOverHom_ext {p : U ⟶ X} {φ ψ : U ⟶ (localizedSigmaCofan fun _ : S => X).pt}
    (hφ : φ ≫ Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : S => X)
      (fun _ => 𝟙 X) = p)
    (hψ : ψ ≫ Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : S => X)
      (fun _ => 𝟙 X) = p)
    (h : ∀ x, index (fun _ : S => X) φ x = index (fun _ : S => X) ψ x) : φ = ψ :=
  (eq_overHom (isLocallyConstant_index _ φ) hφ fun _ => rfl).trans
    (eq_overHom (isLocallyConstant_index _ φ) hψ fun x => (h x).symm).symm

/-- Every locally constant map `c : U → S` is the index map of a morphism over `p : U → X` into
`⊔_{s ∈ S} X`. -/
theorem exists_copiesOverHom (p : U ⟶ X) (c : localizedSpaceFunctor.obj U → S)
    (hc : IsLocallyConstant c) :
    ∃ φ : U ⟶ (localizedSigmaCofan fun _ : S => X).pt,
      φ ≫ Cofan.IsColimit.desc (isColimitLocalizedSigmaCofan fun _ : S => X)
        (fun _ => 𝟙 X) = p ∧ ∀ x, index (fun _ : S => X) φ x = c x :=
  ⟨overHom p c hc, overHom_comp_codiag p c hc, index_overHom p c hc⟩

end OverHom

end Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace
