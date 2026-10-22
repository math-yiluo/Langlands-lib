import Langlands.Representation.Filtration.VanishingStatement
import Langlands.Representation.Classification.SupercuspidalSupport

/-! Absence of quasicuspidal subquotients propagates through finite filtrations. -/

open CategoryTheory

namespace Langlands

universe uR uG uV uF uW

namespace SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]

/-- Descend a morphism through the actual quotient by the kernel of another
morphism with the same source. -/
def kernelLift {P Y Z : SmoothRep.{uR, uG, uV} R G} (φ : P ⟶ Z) (ψ : P ⟶ Y)
    (h : (hom φ).ker ≤ (hom ψ).ker) : quotient P (hom φ).ker ⟶ Y :=
  ofHom
    { toLinearMap := (hom φ).ker.toSubmodule.liftQ (hom ψ).toLinearMap fun _ hv => h hv
      isIntertwining' := fun g => by
        apply Submodule.linearMap_qext
        ext v
        exact Representation.IntertwiningMap.isIntertwining _ _ (hom ψ) g v }

theorem kernelLift_mkQ {P Y Z : SmoothRep.{uR, uG, uV} R G} (φ : P ⟶ Z) (ψ : P ⟶ Y)
    (h : (hom φ).ker ≤ (hom ψ).ker) (v : P) :
    hom (kernelLift φ ψ h) (hom (mkQ P (hom φ).ker) v) = hom ψ v := rfl

/-- If `ψ` is surjective and vanishes on the kernel of `φ`, then the target
of `ψ` is a subquotient of the target of `φ`: the actual quotient of the
common source by the kernel of `φ` embeds in the latter and maps onto the
former. -/
theorem isSubquotient_of_ker_le {P Y Z : SmoothRep.{uR, uG, uV} R G}
    (φ : P ⟶ Z) (ψ : P ⟶ Y) (hψ : Function.Surjective (hom ψ))
    (h : (hom φ).ker ≤ (hom ψ).ker) : IsSubquotient Y Z := by
  refine isSubquotient_iff_exists.mpr
    ⟨quotient P (hom φ).ker, kernelLift φ φ le_rfl, kernelLift φ ψ h, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨x, rfl⟩ := mkQ_surjective P (hom φ).ker x
    obtain ⟨y, rfl⟩ := mkQ_surjective P (hom φ).ker y
    rw [kernelLift_mkQ, kernelLift_mkQ] at hxy
    refine (Submodule.Quotient.eq _).mpr ?_
    change hom φ (x - y) = 0
    rw [map_sub, hxy, sub_self]
  · intro y
    obtain ⟨x, rfl⟩ := hψ y
    exact ⟨hom (mkQ P (hom φ).ker) x, rfl⟩

end SmoothRep

namespace CuspidalSupport

open GeneralLinear Geometric

/-- Quasicuspidality passes to every actual quotient: a surjective intertwiner
induces a surjection of actual unipotent coinvariant modules. -/
theorem isLeviQuasicuspidal_of_surjective {F : Type uF} [Field F] {n : ℕ}
    (B : BlockShape n) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F) V} {σ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hρ : IsLeviQuasicuspidal B ρ) : IsLeviQuasicuspidal B σ := by
  intro S hS
  have := hρ S hS
  refine Function.Surjective.subsingleton
    (f := Representation.Coinvariants.map _ _
      (Jacquet.restrictMap f (refinedUnipotent F B S))) ?_
  intro x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective σ _ x
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Jacquet.mk ρ _ v, rfl⟩

end CuspidalSupport

namespace ObjectRepFiltration

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]
  {M C X : SmoothRep.{uR, uG, uV} R G} {r : ℕ}

/-- The inverse image of a filtration step under an intertwiner into the
filtered representation. -/
def pullStep (s : ObjectRepFiltration (Rep.of M.representation) r) (i : C ⟶ M)
    (k : Fin (r + 1)) : Subrepresentation C.representation where
  toSubmodule := (s.subrepresentation k).toSubmodule.comap (SmoothRep.hom i).toLinearMap
  apply_mem_toSubmodule g v hv := by
    change SmoothRep.hom i (C.representation g v) ∈ s.subrepresentation k
    rw [(SmoothRep.hom i).isIntertwining]
    exact (s.subrepresentation k).apply_mem_toSubmodule g hv

theorem mem_pullStep (s : ObjectRepFiltration (Rep.of M.representation) r)
    (i : C ⟶ M) (k : Fin (r + 1)) (v : C) :
    v ∈ pullStep s i k ↔ SmoothRep.hom i v ∈ s.subrepresentation k := Iff.rfl

/-- The image in `X` of a pulled-back step: the induced filtration of the
subquotient presented by `i` and `q`. -/
def imageStep (s : ObjectRepFiltration (Rep.of M.representation) r) (i : C ⟶ M)
    (q : C ⟶ X) (k : Fin (r + 1)) : Subrepresentation X.representation where
  toSubmodule := (pullStep s i k).toSubmodule.map (SmoothRep.hom q).toLinearMap
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨C.representation g v, (pullStep s i k).apply_mem_toSubmodule g hv,
      Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom q) g v⟩

theorem mem_imageStep (s : ObjectRepFiltration (Rep.of M.representation) r)
    (i : C ⟶ M) (q : C ⟶ X) (k : Fin (r + 1)) (x : X) :
    x ∈ imageStep s i q k ↔ ∃ v ∈ pullStep s i k, SmoothRep.hom q v = x := Iff.rfl

/-- Restriction of `i` from a pulled-back step to the original step. -/
def pullStepRestrict (s : ObjectRepFiltration (Rep.of M.representation) r)
    (i : C ⟶ M) (k : Fin (r + 1)) :
    (SmoothRep.subrepresentation C (pullStep s i k)).representation.IntertwiningMap
      (s.subrepresentation k).toRepresentation where
  toLinearMap := (SmoothRep.hom i).toLinearMap.restrict fun _ hv => hv
  isIntertwining' g := by
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom i) g v.1

/-- If the image of step `j + 1` is everything, the quotient of `X` by the
image of step `j` is a subquotient of any smooth representative of the
`j`th actual graded quotient. -/
theorem isSubquotient_quotient_imageStep
    (s : ObjectRepFiltration (Rep.of M.representation) r) (i : C ⟶ M) (q : C ⟶ X)
    (j : Fin r) (htop : ∀ x : X, x ∈ imageStep s i q j.succ)
    (Q : SmoothRep.{uR, uG, uV} R G)
    (e : (s.gradedRepresentation j).ρ.Equiv Q.representation) :
    SmoothRep.IsSubquotient (SmoothRep.quotient X (imageStep s i q j.castSucc)) Q := by
  let P := SmoothRep.subrepresentation C (pullStep s i j.succ)
  let φ : P ⟶ Q := SmoothRep.ofHom
    (e.toIntertwiningMap.comp ((s.gradedProjection j).hom.comp (pullStepRestrict s i j.succ)))
  let ψ : P ⟶ SmoothRep.quotient X (imageStep s i q j.castSucc) :=
    SmoothRep.subtype C (pullStep s i j.succ) ≫ q ≫
      SmoothRep.mkQ X (imageStep s i q j.castSucc)
  refine SmoothRep.isSubquotient_of_ker_le φ ψ ?_ ?_
  · intro y
    obtain ⟨x, rfl⟩ := SmoothRep.mkQ_surjective X _ y
    obtain ⟨v, hv, rfl⟩ := htop x
    exact ⟨⟨v, hv⟩, rfl⟩
  · intro v hv
    have h1 : (s.gradedProjection j).hom (pullStepRestrict s i j.succ v) = 0 :=
      (map_eq_zero_iff e e.injective).mp hv
    have h2 := (Submodule.Quotient.mk_eq_zero _).mp h1
    change Submodule.Quotient.mk (SmoothRep.hom q v.1) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v.1, h2, rfl⟩

end ObjectRepFiltration

namespace CuspidalSupport

open GeneralLinear

/-- Proof of `PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement`. -/
theorem padicLeviFiltrationNoQuasicuspidalSubquotients :
    PadicLeviFiltrationNoQuasicuspidalSubquotientsStatement.{uV, uF} := by
  intro p _ F T
  let _ := T.topology
  intro n B A r s hs D hD hDq
  obtain ⟨C, i, q, hi, hq⟩ := SmoothRep.isSubquotient_iff_exists.mp hD
  have key : ∀ k : Fin (r + 1), ∀ x : D, x ∈ ObjectRepFiltration.imageStep s i q k := by
    intro k
    induction k using Fin.reverseInduction with
    | last =>
      intro x
      obtain ⟨v, rfl⟩ := hq x
      refine ⟨v, ?_, rfl⟩
      change SmoothRep.hom i v ∈ s.subrepresentation (Fin.last r)
      rw [s.subrepresentation_last]
      trivial
    | cast j ih =>
      obtain ⟨Q, ⟨e⟩, hQ⟩ := hs j
      have hY := hQ _ (ObjectRepFiltration.isSubquotient_quotient_imageStep s i q j ih Q e)
        (isLeviQuasicuspidal_of_surjective B _ (SmoothRep.mkQ_surjective D _) hDq)
      intro x
      have hx : SmoothRep.hom (SmoothRep.mkQ D (ObjectRepFiltration.imageStep s i q j.castSucc))
          x = 0 := Subsingleton.elim _ _
      exact (Submodule.Quotient.mk_eq_zero _).mp hx
  refine ⟨fun x y => ?_⟩
  have hzero : ∀ x : D, x = 0 := fun x => by
    obtain ⟨v, hv, rfl⟩ := key 0 x
    have hv' : SmoothRep.hom i v ∈ s.subrepresentation 0 := hv
    rw [s.subrepresentation_zero] at hv'
    have hv0 : SmoothRep.hom i v = 0 := (Submodule.mem_bot ℂ).mp hv'
    rw [hi (hv0.trans (map_zero _).symm), map_zero]
  rw [hzero x, hzero y]

end CuspidalSupport

end Langlands
