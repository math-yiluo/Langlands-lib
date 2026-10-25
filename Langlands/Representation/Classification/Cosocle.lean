import Langlands.Representation.Classification.CanonicalConstituents
import Langlands.Representation.SubrepresentationLattice
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# The head as the cosocle

For a representation `ρ` of a group `G` over a field `k`, the head kernel of
`Classification/CanonicalConstituents` is the intersection of the maximal
subrepresentations of `ρ`; under the correspondence with group-algebra submodules
it is the Jacobson radical of `ρ.asModule`. Every intertwiner from `ρ` to a
semisimple representation, in any carrier universe, descends uniquely to the head,
and every intertwiner `ρ → σ` induces a map of heads. When `ρ.asModule` has finite
length over `k[G]`, the head has finite length and is semisimple, so it is the
cosocle (maximal semisimple quotient) of `ρ`. The head of a smooth representation
is smooth.
-/

noncomputable section

open scoped MonoidAlgebra

namespace Langlands.Classification

universe uk uG uV uW uU

open Representation.IntertwiningMap (equivLinearMapAsModule)

variable {k : Type uk} [Field k] {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module k V] {ρ : Representation k G V}
variable {W : Type uW} [AddCommGroup W] [Module k W]

section Radical

/-- A surjective intertwiner has an irreducible target exactly when its kernel is a
maximal subrepresentation. -/
theorem isIrreducible_iff_isCoatom_ker {π : Representation k G W}
    (q : ρ.IntertwiningMap π) (hq : Function.Surjective q) :
    Representation.IsIrreducible π ↔ IsCoatom q.ker := by
  have hf : Function.Surjective (equivLinearMapAsModule ρ π q) := hq
  have hker : Subrepresentation.ofSubmodule'
      (LinearMap.ker (equivLinearMapAsModule ρ π q)) = q.ker :=
    SetLike.ext fun _ => Iff.rfl
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    ← ((equivLinearMapAsModule ρ π q).quotKerEquivOfSurjective hf).isSimpleModule_iff,
    isSimpleModule_iff_isCoatom, ← hker]
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.isCoatom_iff _).symm

/-- A vector lies in the head kernel exactly when it lies in every maximal
subrepresentation. -/
theorem mem_headKernel_iff_forall_isCoatom (ρ : Representation k G V) (v : V) :
    v ∈ (headKernel ρ).toSubmodule ↔
      ∀ S : Subrepresentation ρ, IsCoatom S → v ∈ S.toSubmodule := by
  refine ⟨fun hv S hS => ?_, fun h W _ _ π hπ q hq =>
    h q.ker ((isIrreducible_iff_isCoatom_ker q hq).mp hπ)⟩
  let q : ρ.IntertwiningMap (ρ.quotient S.toSubmodule fun g _ hw =>
      S.apply_mem_toSubmodule g hw) :=
    { toLinearMap := S.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hker : q.ker = S :=
    Subrepresentation.toSubmodule_injective (Submodule.ker_mkQ S.toSubmodule)
  have hπ := (isIrreducible_iff_isCoatom_ker q hq).mpr (by rw [hker]; exact hS)
  exact (Submodule.Quotient.mk_eq_zero _).mp (hv _ _ hπ q hq)

/-- The head kernel is the intersection of the maximal subrepresentations. -/
theorem headKernel_eq_sInf_isCoatom (ρ : Representation k G V) :
    headKernel ρ = sInf {S : Subrepresentation ρ | IsCoatom S} := by
  refine Subrepresentation.toSubmodule_injective (Submodule.ext fun v => ?_)
  rw [Subrepresentation.toSubmodule_sInf, mem_headKernel_iff_forall_isCoatom]
  simp only [Submodule.mem_iInf]
  rfl

/-- Under the correspondence with `k[G]`-submodules, the head kernel is the Jacobson
radical of `ρ.asModule`. -/
theorem asSubmodule_headKernel (ρ : Representation k G V) :
    (headKernel ρ).asSubmodule = Module.jacobson k[G] ρ.asModule := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  refine Submodule.ext fun v => (mem_headKernel_iff_forall_isCoatom ρ v).trans ?_
  show _ ↔ v ∈ sInf {m : Submodule k[G] ρ.asModule | IsCoatom m}
  rw [Submodule.mem_sInf]
  exact ⟨fun h m hm => h (e.symm m) ((e.symm.isCoatom_iff m).mpr hm),
    fun h S hS => h (e S) ((e.isCoatom_iff S).mpr hS)⟩

/-- The head kernel is the subrepresentation of the Jacobson radical of
`ρ.asModule`. -/
theorem headKernel_eq_ofSubmodule'_jacobson (ρ : Representation k G V) :
    headKernel ρ = Subrepresentation.ofSubmodule' (Module.jacobson k[G] ρ.asModule) := by
  rw [← asSubmodule_headKernel]
  rfl

/-- The kernel of the head projection, as a `k[G]`-submodule, is the Jacobson
radical. -/
theorem ker_equivLinearMapAsModule_toHead (ρ : Representation k G V) :
    LinearMap.ker (equivLinearMapAsModule ρ (head ρ) (toHead ρ)) =
      Module.jacobson k[G] ρ.asModule := by
  rw [← asSubmodule_headKernel]
  exact SetLike.ext fun _ => Submodule.Quotient.mk_eq_zero _

end Radical

section FiniteLength

/-- The head of a finite-length representation has finite length. -/
theorem isFiniteLength_head (h : IsFiniteLength k[G] ρ.asModule) :
    IsFiniteLength k[G] (head ρ).asModule :=
  h.of_surjective (f := equivLinearMapAsModule ρ (head ρ) (toHead ρ)) (toHead_surjective ρ)

/-- The head of a finite-length representation is semisimple. -/
theorem isSemisimpleRepresentation_head (h : IsFiniteLength k[G] ρ.asModule) :
    Representation.IsSemisimpleRepresentation (head ρ) := by
  have : IsArtinian k[G] (head ρ).asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_head h)).2
  have hf : Function.Surjective (equivLinearMapAsModule ρ (head ρ) (toHead ρ)) :=
    toHead_surjective ρ
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    IsArtinian.isSemisimpleModule_iff_jacobson,
    ← Module.map_jacobson_of_ker_le hf (ker_equivLinearMapAsModule_toHead ρ).le, eq_bot_iff,
    Submodule.map_le_iff_le_comap, Submodule.comap_bot, ker_equivLinearMapAsModule_toHead]

end FiniteLength

section Lift

/-- An irreducible representation is semisimple. -/
theorem isSemisimpleRepresentation_of_isIrreducible {π : Representation k G W}
    (hπ : Representation.IsIrreducible π) : Representation.IsSemisimpleRepresentation π :=
  inferInstance

/-- The head kernel lies in the kernel of every intertwiner to a semisimple
representation, with carrier in any universe. -/
theorem headKernel_le_ker_of_isSemisimpleRepresentation {σ : Representation k G W}
    (hσ : Representation.IsSemisimpleRepresentation σ) (f : ρ.IntertwiningMap σ) :
    (headKernel ρ).toSubmodule ≤ LinearMap.ker f.toLinearMap := by
  have := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp hσ
  have h := IsSemisimpleModule.jacobson_le_ker _ _ _ _ (equivLinearMapAsModule ρ σ f)
  rw [← asSubmodule_headKernel] at h
  exact fun v hv => h hv

/-- The head kernel lies in the kernel of every intertwiner to an irreducible
representation, with carrier in any universe. -/
theorem headKernel_le_ker_of_isIrreducible {π : Representation k G W}
    (hπ : Representation.IsIrreducible π) (f : ρ.IntertwiningMap π) :
    (headKernel ρ).toSubmodule ≤ LinearMap.ker f.toLinearMap :=
  headKernel_le_ker_of_isSemisimpleRepresentation
    (isSemisimpleRepresentation_of_isIrreducible hπ) f

/-- The intertwiner from the head through which an intertwiner to a semisimple
representation factors. -/
def headLift {σ : Representation k G W} (f : ρ.IntertwiningMap σ)
    (hσ : Representation.IsSemisimpleRepresentation σ) :
    (head ρ).IntertwiningMap σ where
  toLinearMap := (headKernel ρ).toSubmodule.liftQ f.toLinearMap
    (headKernel_le_ker_of_isSemisimpleRepresentation hσ f)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext v
    exact Representation.IntertwiningMap.isIntertwining _ _ f g v

@[simp]
theorem headLift_toHead {σ : Representation k G W} (f : ρ.IntertwiningMap σ)
    (hσ : Representation.IsSemisimpleRepresentation σ) (v : V) :
    headLift f hσ (toHead ρ v) = f v :=
  rfl

@[simp]
theorem headLift_comp_toHead {σ : Representation k G W} (f : ρ.IntertwiningMap σ)
    (hσ : Representation.IsSemisimpleRepresentation σ) :
    (headLift f hσ).comp (toHead ρ) = f :=
  rfl

/-- The descended intertwiner is the only one whose composite with the head
projection is `f`. -/
theorem headLift_unique {σ : Representation k G W} {f : ρ.IntertwiningMap σ}
    (hσ : Representation.IsSemisimpleRepresentation σ)
    {g : (head ρ).IntertwiningMap σ} (hg : g.comp (toHead ρ) = f) :
    g = headLift f hσ := by
  ext v
  exact DFunLike.congr_fun hg v

/-- Universal property of the head: every intertwiner to a semisimple
representation factors uniquely through the head projection. -/
theorem existsUnique_comp_toHead {σ : Representation k G W}
    (hσ : Representation.IsSemisimpleRepresentation σ) (f : ρ.IntertwiningMap σ) :
    ∃! g : (head ρ).IntertwiningMap σ, g.comp (toHead ρ) = f :=
  ⟨headLift f hσ, headLift_comp_toHead f hσ, fun _ hg => headLift_unique hσ hg⟩

end Lift

section Map

variable {U : Type uU} [AddCommGroup U] [Module k U]

/-- An intertwiner maps the head kernel of its source into the head kernel of its
target. -/
theorem headKernel_le_comap {σ : Representation k G W} (f : ρ.IntertwiningMap σ) :
    (headKernel ρ).toSubmodule ≤ (headKernel σ).toSubmodule.comap f.toLinearMap := by
  have h := Module.le_comap_jacobson (equivLinearMapAsModule ρ σ f)
  rw [← asSubmodule_headKernel, ← asSubmodule_headKernel] at h
  exact fun v hv => h hv

/-- The map of heads induced by an intertwiner. -/
def headMap {σ : Representation k G W} (f : ρ.IntertwiningMap σ) :
    (head ρ).IntertwiningMap (head σ) where
  toLinearMap := (headKernel ρ).toSubmodule.mapQ (headKernel σ).toSubmodule f.toLinearMap
    (headKernel_le_comap f)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext v
    exact congrArg (toHead σ) (Representation.IntertwiningMap.isIntertwining _ _ f g v)

@[simp]
theorem headMap_toHead {σ : Representation k G W} (f : ρ.IntertwiningMap σ) (v : V) :
    headMap f (toHead ρ v) = toHead σ (f v) :=
  rfl

theorem headMap_comp_toHead {σ : Representation k G W} (f : ρ.IntertwiningMap σ) :
    (headMap f).comp (toHead ρ) = (toHead σ).comp f :=
  rfl

/-- The induced map is the only intertwiner of heads compatible with the head
projections. -/
theorem headMap_unique {σ : Representation k G W} {f : ρ.IntertwiningMap σ}
    {g : (head ρ).IntertwiningMap (head σ)} (hg : g.comp (toHead ρ) = (toHead σ).comp f) :
    g = headMap f := by
  ext v
  exact DFunLike.congr_fun hg v

@[simp]
theorem headMap_id (ρ : Representation k G V) :
    headMap (Representation.IntertwiningMap.id ρ) = Representation.IntertwiningMap.id (head ρ) :=
  (headMap_unique (f := Representation.IntertwiningMap.id ρ)
    (g := Representation.IntertwiningMap.id (head ρ)) rfl).symm

theorem headMap_comp {σ : Representation k G W} {τ : Representation k G U}
    (f : ρ.IntertwiningMap σ) (g : σ.IntertwiningMap τ) :
    headMap (g.comp f) = (headMap g).comp (headMap f) :=
  (headMap_unique (f := g.comp f) (g := (headMap g).comp (headMap f)) rfl).symm

end Map

section Maximal

/-- In finite length, a surjective intertwiner onto a semisimple representation whose
kernel lies in the kernel of every intertwiner to a semisimple representation with
carrier in the universe of `V` has the head kernel as its kernel. -/
theorem headKernel_eq_ker_of_forall_le_ker (h : IsFiniteLength k[G] ρ.asModule)
    {π : Representation k G W} (hπ : Representation.IsSemisimpleRepresentation π)
    (q : ρ.IntertwiningMap π)
    (hq : ∀ (W' : Type uV) [AddCommGroup W'] [Module k W'] (σ : Representation k G W'),
      Representation.IsSemisimpleRepresentation σ → ∀ f : ρ.IntertwiningMap σ,
        LinearMap.ker q.toLinearMap ≤ LinearMap.ker f.toLinearMap) :
    (headKernel ρ).toSubmodule = LinearMap.ker q.toLinearMap :=
  le_antisymm (headKernel_le_ker_of_isSemisimpleRepresentation hπ q)
    ((hq _ (head ρ) (isSemisimpleRepresentation_head h) (toHead ρ)).trans
      (ker_toHead ρ).le)

/-- In finite length, the head is equivalent to every maximal semisimple quotient. -/
theorem nonempty_headEquiv_of_forall_le_ker (h : IsFiniteLength k[G] ρ.asModule)
    {π : Representation k G W} (hπ : Representation.IsSemisimpleRepresentation π)
    (q : ρ.IntertwiningMap π) (hsurj : Function.Surjective q)
    (hq : ∀ (W' : Type uV) [AddCommGroup W'] [Module k W'] (σ : Representation k G W'),
      Representation.IsSemisimpleRepresentation σ → ∀ f : ρ.IntertwiningMap σ,
        LinearMap.ker q.toLinearMap ≤ LinearMap.ker f.toLinearMap) :
    Nonempty ((head ρ).Equiv π) :=
  ⟨headEquivOfSurjective q hsurj (headKernel_eq_ker_of_forall_le_ker h hπ q hq)⟩

end Maximal

/-- The head of a smooth representation is smooth. -/
theorem isSmooth_head [TopologicalSpace G] (hρ : IsSmooth ρ) : IsSmooth (head ρ) :=
  isSmooth_of_surjective (toHead ρ) (toHead_surjective ρ) hρ

end Langlands.Classification

namespace Langlands.SmoothRep

universe uk uG uV

open CategoryTheory
open scoped MonoidAlgebra

variable {k : Type uk} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]
variable {A B C : SmoothRep.{uk, uG, uV} k G}

/-- The head of a finite-length smooth representation has finite length. -/
theorem HasFiniteLength.headQuotient (h : A.HasFiniteLength) :
    A.headQuotient.HasFiniteLength :=
  Classification.isFiniteLength_head h

/-- The head of a finite-length smooth representation is semisimple. -/
theorem isSemisimpleRepresentation_headQuotient (h : A.HasFiniteLength) :
    Representation.IsSemisimpleRepresentation A.headQuotient.representation :=
  Classification.isSemisimpleRepresentation_head h

/-- The morphism from the head through which a morphism to a semisimple smooth
representation factors. -/
def headQuotientLift (f : A ⟶ B)
    (hB : Representation.IsSemisimpleRepresentation B.representation) :
    A.headQuotient ⟶ B :=
  ofHom (Classification.headLift (hom f) hB)

@[simp]
theorem toHeadQuotient_headQuotientLift (f : A ⟶ B)
    (hB : Representation.IsSemisimpleRepresentation B.representation) :
    A.toHeadQuotient ≫ headQuotientLift f hB = f :=
  rfl

theorem headQuotientLift_unique {f : A ⟶ B}
    (hB : Representation.IsSemisimpleRepresentation B.representation)
    {g : A.headQuotient ⟶ B} (hg : A.toHeadQuotient ≫ g = f) :
    g = headQuotientLift f hB :=
  congrArg ofHom (Classification.headLift_unique hB (congrArg hom hg))

/-- The morphism of heads induced by a morphism of smooth representations. -/
def headQuotientMap (f : A ⟶ B) : A.headQuotient ⟶ B.headQuotient :=
  ofHom (Classification.headMap (hom f))

@[simp]
theorem toHeadQuotient_headQuotientMap (f : A ⟶ B) :
    A.toHeadQuotient ≫ headQuotientMap f = f ≫ B.toHeadQuotient :=
  rfl

@[simp]
theorem headQuotientMap_id (A : SmoothRep.{uk, uG, uV} k G) :
    headQuotientMap (𝟙 A) = 𝟙 A.headQuotient :=
  congrArg ofHom (Classification.headMap_id A.representation)

theorem headQuotientMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    headQuotientMap (f ≫ g) = headQuotientMap f ≫ headQuotientMap g :=
  congrArg ofHom (Classification.headMap_comp (hom f) (hom g))

variable (k G) in
/-- The head as an endofunctor of smooth representations. -/
@[simps]
def headQuotientFunctor : SmoothRep.{uk, uG, uV} k G ⥤ SmoothRep.{uk, uG, uV} k G where
  obj := headQuotient
  map := headQuotientMap
  map_id := headQuotientMap_id
  map_comp := headQuotientMap_comp

end Langlands.SmoothRep
